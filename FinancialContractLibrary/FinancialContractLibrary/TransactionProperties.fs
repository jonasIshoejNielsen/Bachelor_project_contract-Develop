module TransactionProperties
open ContractTypes
open ContractHelperFunctions
open ContractEval
open System

let match2Options t1 t2 dif bothNone op =
    match t1, t2 with
    | None, None -> bothNone
    | Some v1, Some v2 -> op v1 v2
    | Some v1,_ | None, Some v1 -> dif


///<summary>Exchange currency to noncurrency value</summary>
let currencyExchange currencyExchangeValue (curr: Currency) =
    match Map.tryFind curr currencyExchangeValue with
    | Some exc  -> (*) exc
    | None      -> (*) 1.0

let bothEmptyThenTrue parties1 parties2 = (parties1|>Set.count =0 && parties2 |> Set.count = 0)

let TransactionsDayFold f acc (lst: (int * Transaction list) list) =
    lst
    |> List.fold (fun acc (i, v) -> v |> List.fold (fun acc (part1, part2, v, curr) -> f acc (i,(part1, part2, v, curr))) acc) acc
let TransactionsPartyFold f acc lst =
    lst
    |> List.fold (fun acc (p, vlst) -> vlst |> List.fold (fun acc (i, (part1, part2, v, curr)) -> f acc (i, (part1, part2, v, curr))) acc) acc

let addValueToMap currencyExchangeValue curr v p map= 
    let value = currencyExchange currencyExchangeValue curr v
    match (Map.tryFind p map) with 
    | None -> 
        (Map.add (p) (value) map) 
    | Some (v1) ->
        (Map.add (p) (v1+value) map)

let currencyExchangeDefault () = Map.empty

let transactionsFilter t f =
    match t with
    | None -> None
    | Some t -> 
        match t with
        | TransactionsDay t -> 
            t
            |> List.map(fun (d,lst) -> (d, lst |> List.filter f))
            |> List.filter(fun (_,lst) -> lst |> List.isEmpty |> not)
            |> TransactionsDay
            |> Some
        | TransactionsParty (t1, t2) -> 
            let mapFilter (t: PartyTransactions) :PartyTransactions =
                t 
                |> List.map(fun (p,lst) -> (p, lst |> List.filter (fun (_, v) -> v |> f)))
                |> List.filter(fun (_,lst) -> lst |> List.isEmpty |> not)
            (mapFilter t1, mapFilter t2) |> TransactionsParty |> Some

///<summary>The transactions with all payments of value zero removed</summary>
let transactionsWithoutZeroPays t =
    transactionsFilter t (fun (_,_,v,_) -> v =~0.0 |> not)
    
///<summary>The transactions with all payments where the 2 parties are the same removed</summary>
let transactionsWithoutPayToPayee t =
    transactionsFilter t (fun (p1,p2,_,_) -> p1 <> p2)

///<summary>test that t11=t21 and t12=t22</summary>     
let equalMap (m1, m2)=
    let equal m1 m2 =
        m1
        |>Map.toList
        |> List.exists(fun (k,v) ->
            match Map.tryFind (k) m2 with
            | None -> false
            | Some (f) -> f =~ v
           )
    (equal m1 m2)

///<summary>The total value a party gives ,  the total value a party gets from a transaction</summary>
let valueForParty p currencyExchangeValue (t:Transactions) =
    match t with
    | TransactionsDay t -> 
        let f (accGive,accGet) (_,(p1,p2,v,c)) = 
            let valIfEqual px = if px=p then currencyExchange currencyExchangeValue c v else 0.0
            (accGive + valIfEqual p2, accGet + valIfEqual p1)
        t |> TransactionsDayFold f (0.0, 0.0)
    | TransactionsParty (t1, t2) -> 
        let rec getVal cp =
            match cp with
            | [] -> 0.0
            | (cp,t)::_ when cp = p -> 
                t |> List.fold (fun acc (_,(_,_, v, c)) -> acc + (currencyExchange currencyExchangeValue c v)) 0.0
            | _ :: pt -> getVal pt 
        (getVal t2, getVal t1) 

///<summary>sum of the value that a party gives substractd from what a party gets from a transaction</summary>
let cashFlowForParty p currencyExchangeValue (t:Transactions) =
    t |> valueForParty p currencyExchangeValue 
    |> fun (resGive,resGet) -> resGive - resGet

///<summary>Map mapping party to value given , Map mapping party to value recieved</summary>
let valuesForAllParties currencyExchangeValue (t:Transactions) =
    match t with
    | TransactionsDay t -> 
        let f (map1, map2) (i, (part1, part2, v, curr)) = 
            let createMap p map = addValueToMap currencyExchangeValue curr v p map
            ((createMap part1 map1), (createMap part2 map2))
        t |> TransactionsDayFold f (Map.empty, Map.empty)
    | TransactionsParty (t1, t2) ->
        let f fstOrSnd acc (i, (part1, part2, v, curr)) =
            addValueToMap currencyExchangeValue curr v (fstOrSnd (part1, part2)) acc
        (t1 |> TransactionsPartyFold (f fst) Map.empty, t2 |> TransactionsPartyFold (f snd) Map.empty)

///<summary>Gives set of parties pressent in a Transactions</summary>
let setOfPartiesFromTrans (t:Transactions) addIfPayZero=
    match t with
    | TransactionsDay t ->
        t |> TransactionsDayFold (fun acc (_,(p1, p2,v,_)) -> if addIfPayZero || not( v =~ 0.0) then acc |> Set.add p1 |> Set.add p2 else acc) Set.empty
    | TransactionsParty(m1,m2) ->
        let rec getParty t acc=
            match t with
            | [] -> acc
            | (cp,lst)::tl ->
                if addIfPayZero
                then getParty tl (Set.add cp acc)
                else getParty tl (if lst |> List.exists(fun (_,(_, _,v,_)) -> v =~ 0.0 |> not) then Set.add cp acc else acc)
                
        Set.empty |> getParty m1 |> getParty m2
///<summary>Gives set of parties pressent in either or both Transactions</summary>
let setOfParties2 t1 t2 addIfPayZero = Set.union (setOfPartiesFromTrans t1 addIfPayZero) (setOfPartiesFromTrans t2 addIfPayZero)
///<summary>Test if any party makes f true</summary>
let listOfPartiesExists t1 t2 addIfPayZero f = setOfParties2 t1 t2 addIfPayZero |> Set.exists f

type partyToDayToValue = Map<Party, Map<Date, float>> 
type transacitonsMaps = partyToDayToValue* partyToDayToValue
///<summary>Convert each Transactions to 2 maps each. first map in each tupple is maps party to map mapping days to transactions with party giving, second map in each tupple maps same way but for parties receiving</summary>
let convertTransactionsToMaps currencyExchangeValue t1 t2 : (transacitonsMaps*transacitonsMaps)= 
    let createMap p m d v =     // (p, [(2, value); (3, value); (4, value)]) list = (p, [(2, value); (3, value); (4, value)]) list
        let addToInnerMap m2 =
            match (Map.tryFind d m2) with 
            | None    -> Map.add p (Map.add d v m2) m
            | Some v2 -> Map.add p (Map.add d (v+v2) m2) m
        match (Map.tryFind p m) with | Some m2 -> m2 | _ -> Map.empty
        |> addToInnerMap

    let applyFtoBothAndCreateTupple tV1 tV2 f = (tV1 |> f, tV2 |> f)
    let addInstanceToMaps (m1,m2) (d,(p1,p2,v,c)) =
        (createMap p1 m1 d (currencyExchange currencyExchangeValue c v)), (createMap p2 m2 d (currencyExchange currencyExchangeValue c v))

    match t1,t2 with
    | TransactionsDay tV1, TransactionsDay tV2              -> (Map.empty, Map.empty) |> TransactionsDayFold   addInstanceToMaps |> applyFtoBothAndCreateTupple tV1 tV2
    | TransactionsParty (tV1, _), TransactionsParty (tV2,_) -> (Map.empty, Map.empty) |> TransactionsPartyFold addInstanceToMaps |> applyFtoBothAndCreateTupple tV1 tV2
    | _, _ -> failwith "UnSpecified"
///<summary>Gives number of pays and receives for party p</summary>
let numberOfPaysForParty p t1 =   
    match t1 with
    | TransactionsDay tV1 ->
        let collectPays = TransactionsDayFold (fun acc (d,(p1,p2,v,c)) -> if p=p1 then acc + 1 else acc) 0
        let collectReceives = TransactionsDayFold (fun acc (d,(p1,p2,v,c)) -> if p=p2 then acc + 1 else acc) 0
        tV1 |> collectPays,  tV1 |> collectReceives
    | TransactionsParty (tV11, tV12) -> 
        let collectPay = List.fold (fun acc (p2, lst) -> if p=p2 then List.length lst else acc ) 0
        tV11 |> collectPay,  tV12 |> collectPay



///<summary>Test that value of two contracts fullfil: op (value of t1) (value of t2)</summary>
let compare p currencyExchangeValue t1 t2 op =
    let val1 = cashFlowForParty p currencyExchangeValue t1
    let val2 = cashFlowForParty p currencyExchangeValue t2
    op val1 val2

///<summary>Property party p gets less cashflow in t1 than in t2</summary>
let lessCashFlow p currencyExchangeValue t1 t2 =
    fun t1 t2 -> compare p currencyExchangeValue t1 t2 (<)
    |> match2Options t1 t2 false true

///<summary>Property party p gets same cashflow in both transactions</summary>
let equalCashFlow p currencyExchangeValue t1 t2 =
    fun t1 t2 ->
        compare p currencyExchangeValue t1 t2 (=~)
    |> match2Options t1 t2 false true

///<summary>Property that all parties gets same cashflow in both transactions</summary>
let equalTransactions currencyExchangeValue t1 t2 =
    fun t1' t2' ->
        fun p -> not (equalCashFlow p currencyExchangeValue t1 t2) 
        |> listOfPartiesExists t1' t2' true
        |> not
    |> match2Options t1 t2 false true 
    
///<summary>Property that a cashflow in one is equal to the cashflow in other, ignoring signed value of cash</summary>
let equalNegativeContract currencyExchangeValue t1 t2 =
        let negated p t1 t2 = 
            compare p currencyExchangeValue t1 t2 (fun v1 v2 -> Math.Abs(v1) =~ Math.Abs(v2))
        listOfPartiesExists t1 t2 true (fun p -> not (negated p t1 t2) )
        |> not
///<summary>Property that 2 transactions have same list of parties</summary>
let equalPartiesTransactions t1 t2 addIfPayZero = 
    fun t1 t2 -> Set.difference (setOfPartiesFromTrans t1 addIfPayZero) (setOfPartiesFromTrans t2 addIfPayZero) |> Set.isEmpty
    |> match2Options t1 t2 false true

(*
let equalExchangeList translst1 translst2 =
    let rec inner lst1 lst2  =
        match lst1, lst2 with
            | (_, _, v1, curr1)::xs, (_, _, v2, curr2)::x1 ->
                if currencyExchange v1 curr1 = currencyExchange v2 curr2
                then inner xs x1
                else false
            | [],[] -> true
            | _,_ ->  false
    inner translst1 translst2 *)

///<summary>Property that all parties gets same cashflow in both transactions and at same time</summary>
let exactEqualTransaction currencyExchangeValue (t1: Transactions Option) (t2: Transactions Option) =    // days = days1 && sum1 = sum2
    let compare2Maps p (m1,m2) (m12,m22) =
        match Map.tryFind p m1, Map.tryFind p m2, Map.tryFind p m12, Map.tryFind p m22 with
        | Some map, Some map1, Some map2, Some map3  -> equalMap (map, map2) && equalMap (map1, map3)
        | Some map1, _, Some map2, _
        | _, Some map1, _, Some map2                 -> equalMap (map1, map2)
        | _                                          -> false

    fun t1 t2 ->
        let ((mapT1Get,mapT1Give), (mapT2Get,mapT2Give)) =
             convertTransactionsToMaps currencyExchangeValue t1 t2
        fun party -> (compare2Maps party (mapT1Get, mapT1Give) (mapT2Get, mapT2Give))
        |> listOfPartiesExists t1 t2 true
    |> match2Options t1 t2 false true 

///<summary>Property that transactions has equal number of pays and receives for party p</summary>
let equalNumberOfPaysForParty p t1 t2 =   
    fun t1 t2 -> 
        let givesT1, receivesT1 = numberOfPaysForParty p t1
        let givesT2, receivesT2 = numberOfPaysForParty p t1
        (givesT1 = givesT2) && (receivesT1 = receivesT2)
    |> match2Options t1 t2 false true

///<summary>Property that transaction has equal number of pays and receives for all parties</summary>
let equalNumberOfPays t1 t2 =   
    fun t1 t2 ->
        let foldFunc p =
            let givesT1, receivesT1 = numberOfPaysForParty p t1
            let givesT2, receivesT2 = numberOfPaysForParty p t1
            (givesT1 = givesT2) && (receivesT1 = receivesT2)
        setOfParties2 t1 t2 true
        |> Set.exists(foldFunc >> not)
        |> not
    |> match2Options t1 t2 false true

(*
let allPartyLessCashFlow (t1: Transactions) (t2: Transactions) =
    let map =
        setOfParties2 t1 t2
        |> Set.fold (fun acc p ->
            let less = (lessCashFlow p t1 t2)
            printfn "less %A" less;
            match Map.tryFind p acc with
            | None -> (Map.add (p) less acc)
            | Some (b) ->
                match less, b with
                | false, false -> acc
                | true, false -> (Map.add (p) less acc) 
                | false, true -> acc
                | true, true -> acc
        ) Map.empty
    printfn "map %A" map
    map |> Map.toList
    |> List.exists (fun (k,v) ->
        v = false
    )
    |> not
*)

///<summary>Test if predicate is true for value v1, e.g. GTV(v) -> v1 > v</summary>
let valPredicate pv curr currencyExchangeValue v1 = 
    let helperFunction v op = op (currencyExchange currencyExchangeValue curr v) v1
    match pv with
    | EQV (v)   -> helperFunction v (=~)
    | GTV (v)   -> helperFunction v (<)
    | GTEV (v)  -> helperFunction v (<=~)
    | LTV (v)   -> helperFunction v (>)
    | LTEV (v)  -> helperFunction v (>=~)

///<summary>Test if predicate is true for value d1</summary>
let datePredicate dp d1 = 
    match dp with
    | EQD (d)   -> d = d1
    | GTD (d)   -> d < d1
    | GTED (d)  -> d <= d1
    | LTD (d)   -> d > d1
    | LTED (d)  -> d >= d1
let evalPredicate (d, (_, _, v, curr)) currencyExchangeValue pre =
    let rec aux pre acc c =
        if not acc then false|> c
        else 
            match pre with 
            | PredDate (pd)             -> d |> datePredicate pd |> c
            | PredVal  (pv,pcurr)       -> v |> currencyExchange currencyExchangeValue curr |> valPredicate pv pcurr currencyExchangeValue |> c
            | PredAnd(pre1, pre2)       -> aux pre1 acc (fun acc -> aux pre2 acc c)
            | PredIF(pre1, pre2, pre3)  -> aux pre1 acc (fun acc -> if acc then aux pre2 true c else aux pre3 true c)
            | PredOr(pre1, pre2)        -> aux pre1 acc (fun acc -> if acc then true |>c else aux pre2 true c)
            | PredNot(pre1)             -> aux pre1 acc (fun acc -> acc |> not)
            | PredBool(b)               -> b |> c
    aux pre true id

///<summary>Property that predicates are true for party part</summary>
let evalPredicateTest t part (condition, forHowMany) currencyExchangeValue= 
    let testPredicate acc1 (d, (_, part2, v, curr)) =
        if not (part = part2) then acc1
        else (evalPredicate (d, ((), part2, v, curr)) currencyExchangeValue condition) :: acc1
    
    let exists f =
        match forHowMany with
        | ForAll        -> f |> List.exists not |> not
        | ForAtleastOne -> f |> List.exists id 
        | ForI i        -> f |> List.filter id |> List.length |> (=) i
                
    match t with
    | None -> true
    | Some t ->
        match t with
        | TransactionsDay t1        -> exists (TransactionsDayFold   testPredicate [] t1)
        | TransactionsParty (t1,_)  -> exists (TransactionsPartyFold testPredicate [] t1)

///<summary>Property that combines as many properties as possible showing other version of exact equal</summary>
let allProperties currencyExchangeValue (t1, t2) =
    match t1,t2 with
    | Some t1',Some t2' ->
        let parties1 = setOfPartiesFromTrans t1' true
        let parties2 = setOfPartiesFromTrans t1' true
        if bothEmptyThenTrue parties1 parties2 then true
        else
            let (m1give, m1get) = (valuesForAllParties currencyExchangeValue t1')
            let (m2give, m2get) = (valuesForAllParties currencyExchangeValue t2')
            equalMap (m1give, m2give) 
            >>= (fun _-> (equalMap (m1get, m2get)))
            >>= (fun _-> (parties1 = parties2))
            >>= (fun _-> (equalTransactions currencyExchangeValue t1 t2))
            >>= (fun _-> (exactEqualTransaction currencyExchangeValue t1 t2))
            >>= (fun _-> (equalNegativeContract currencyExchangeValue t1' t2'))
    | None, None -> true
    | _ -> false 