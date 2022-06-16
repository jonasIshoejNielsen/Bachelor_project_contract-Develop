module ContractSimplify
    open ContractTypes
    open ContractHelperFunctions
    
    let unpack1 f1 v1 acc c                      = f1 v1 acc (fun acc -> acc|>c)
    let unpack2 f1 v1 f2 v2 acc c                = f1 v1 acc (fun acc -> f2 v2 acc (fun acc -> acc|>c))
    let unpack3 f1 v1 f2 v2 f3 v3 acc c          = f1 v1 acc (fun acc -> f2 v2 acc (fun acc -> f3 v3 acc (fun acc -> acc|>c)))
    let unpack4 f1 v1 f2 v2 f3 v3 f4 v4 acc c    = f1 v1 acc (fun acc -> f2 v2 acc (fun acc -> f3 v3 acc (fun acc -> f4 v4 acc (fun acc -> acc|>c))))
    
    ///<summary>Collect list variables</summary>
    let rec getListOfLetTypesR r acc c=
        match r with
        | Real _
        | ObsReal _         -> acc |> c
        | VarR n            ->
            let (accR, accB, accC) = acc
            (Set.add n accR, accB, accC) |> c
        | CallR (n, args)   ->
            let (accR, accB, accC) = args  |> List.fold (fun acc v ->  match v with | VReal r -> getListOfLetTypesR r acc id  |_ -> acc) acc
            (Set.add n accR, accB, accC) |> c
        | FoldReal(n, v, ac, i, di) -> unpack4 getListOfLetTypesR v getListOfLetTypesR ac getListOfLetTypesR i getListOfLetTypesR di  acc c
        | Add (r1, r2)      -> unpack2 getListOfLetTypesR r1 getListOfLetTypesR r2 acc c
        | Sub (r1, r2)      -> unpack2 getListOfLetTypesR r1 getListOfLetTypesR r2 acc c 
        | Mul (r1, r2)      -> unpack2 getListOfLetTypesR r1 getListOfLetTypesR r2 acc c 
        | Max (r1, r2)      -> unpack2 getListOfLetTypesR r1 getListOfLetTypesR r2 acc c
        | Pow (r1, f)       -> unpack1 getListOfLetTypesR r1 acc c 
        
    ///<summary>Collect list variables</summary>
    let rec getListOfLetTypesB bool acc c =   
        match bool with
        | Bool _
        | ObsBool _         -> acc |> c
        | BAnd(b1,b2)       -> unpack2 getListOfLetTypesB b1 getListOfLetTypesB b2 acc c
        | BOr(b1,b2)        -> unpack2 getListOfLetTypesB b1 getListOfLetTypesB b2 acc c
        | BNot(b1)          -> unpack1 getListOfLetTypesB b1 acc c
        | RLT(r1,r2)        -> unpack2 getListOfLetTypesR r1 getListOfLetTypesR r2 acc c
        | RGT(r1,r2)        -> unpack2 getListOfLetTypesR r1 getListOfLetTypesR r2 acc c
        | REQ(r1,r2)        -> unpack2 getListOfLetTypesR r1 getListOfLetTypesR r2 acc c
        | RLTEQ(r1,r2)      -> unpack2 getListOfLetTypesR r1 getListOfLetTypesR r2 acc c
        | RGTEQ(r1,r2)      -> unpack2 getListOfLetTypesR r1 getListOfLetTypesR r2 acc c
        | BoolIf(b1,b2,b3)  -> unpack3 getListOfLetTypesB b1 getListOfLetTypesB b2 getListOfLetTypesB b3 acc c
        | VarB n            ->
            let (accR, accB, accC) = acc
            (accR, Set.add n accB, accC) |> c
        | CallB (n, args)   ->
            let (accR, accB, accC) = 
                args 
                |> List.fold (fun acc v ->  match v with  | VCon c ->  acc | VReal r -> getListOfLetTypesR r acc  id  | VBool b -> getListOfLetTypesB b acc id) acc
            (accR, Set.add n accB, accC) |> c
        | FoldBool(n, v, ac, i, di) -> unpack4 getListOfLetTypesB v getListOfLetTypesB ac getListOfLetTypesR i getListOfLetTypesR di  acc c


    
    ///<summary>Remove uncalled LetType initiations</summary>
    let removeLetTypesC con =
        let rec aux con acc c=
            
            let unpack1 v1 op acc c         = aux v1 acc (fun (acc, v1) -> (acc, op v1)|>c)
            let unpack2 v1 v2 op acc c      = aux v1 acc (fun (acc, v1) -> aux v2 acc (fun (acc, v2) -> (acc, op (v1, v2))|>c))
            let unpackFunction n eRhs eBody f1 con setLocation =
                (fun (acc,eBody) -> if acc |> setLocation |> Set.contains n  then f1 eRhs acc id |> (fun acc -> (acc, con) |> c) else (acc,eBody) |>c  )
                |> aux eBody acc

            match con with
            | Zero                                      -> (acc,Zero) |> c
            | Pay (curr, value, date, part1, part2)     -> (getListOfLetTypesR value acc id , con) |>c
            | And (con1, con2)                          -> unpack2 con1 con2 And acc c
            | Scale (con, i)                            -> getListOfLetTypesR i acc id |> (fun acc ->  unpack1 con (fun v1 -> Scale (v1, i)) acc c)
            | Shift (con, d)                            -> unpack1 con (fun v1 -> Shift (v1, d)) acc c
            | If (b, con1, con2)                        -> getListOfLetTypesB b acc id |> (fun acc ->  unpack2 con1 con2 (fun (v1,v2) -> If(b,v1,v2)) acc c)
            | IfWithin (b, date, con1, con2)            -> getListOfLetTypesB b acc id |> (fun acc ->  unpack2 con1 con2 (fun (v1,v2) -> IfWithin(b,date,v1,v2)) acc c)
            | IfUnbound (b, con1)                       -> getListOfLetTypesB b acc id |> (fun acc ->  unpack1 con1 (fun v1 -> IfUnbound (b, v1)) acc c)
            | VarC n                                    -> 
                let (accR, accB, accC) = acc
                ((accR, accB, Set.add n accC), VarC n) |> c
            | CallC (n, args)                           ->
                args 
                |> List.fold (fun acc v ->  match v with  | VCon c ->  aux c acc id |> fst | VReal r -> getListOfLetTypesR r acc id  | VBool b -> getListOfLetTypesB b acc id) acc
                |> fun (accR, accB, accC) -> ((accR, accB, Set.add n accC), CallC (n, args)) |> c
            | IterCon(n, v, i, di)                      -> aux v acc (fun (acc, v1) -> (acc, IterCon(n, v1, i, di)) |> c)
            | LetR (n, eRhs, eBody)
            | LetFunR(n, _, eRhs, eBody)                -> unpackFunction n eRhs eBody getListOfLetTypesR con (fun (v1,v2,v3)->v1)
            | LetB (n, eRhs, eBody)
            | LetFunB(n, _, eRhs, eBody)                -> unpackFunction n eRhs eBody getListOfLetTypesB con  (fun (v1,v2,v3)->v2)
            | LetC (n, eRhs, eBody)                     -> aux eBody acc (fun ((accR, accB, accC), eBody) -> if accC |> Set.contains n |> not then ((accR, accB, accC),eBody) |>c else aux eRhs (accR, accB, accC) (fun (acc, eRhs) ->  (acc,LetC (n, eRhs, eBody)) |> c))
            | LetFunC(n, args, eRhs, eBody)             -> aux eBody acc (fun ((accR, accB, accC), eBody) -> if accC |> Set.contains n |> not then ((accR, accB, accC),eBody) |>c else aux eRhs acc (fun (acc, eRhs) ->  (acc,LetFunC (n, args, eRhs, eBody)) |> c))
            
        
        aux con (Set.empty, Set.empty, Set.empty) id |> snd


    
    ///<summary>Simplify parameter list</summary>
    let simplifyValueList simB simR simC lst = 
        lst
        |> List.map (fun v1 -> match v1 with | VBool b -> simB b |> VBool | VReal r -> simR r |> VReal | VCon c -> simC c |> VCon ) 
    
    type BoolValue = | Different of Bool | Always of bool
    type RealValue = | DifferentR of Real | AlwaysF of float
    
    ///<summary>Simplify a Real</summary>
    let simplifyR r = 
        let toReal r = match r with | AlwaysF r -> Real r | DifferentR r -> r
        let compareTwoReals v1 v2 op real =
            match v1,v2 with
            | AlwaysF r1, AlwaysF r2       -> AlwaysF (op r1 r2)
            | DifferentR r1, AlwaysF r2    -> real (r1, Real r2) |> DifferentR
            | AlwaysF r1, DifferentR r2    -> real (Real r1, r2) |> DifferentR
            | DifferentR r1, DifferentR r2 -> real (r1, r2) |> DifferentR
        let compareSecondWithComp v1 v2 comp res = 
            match res, v2 with | AlwaysF _,_ -> res | _,AlwaysF v2 when v2 =~ comp -> v1 | _ -> res
        
        let compareOne r op f = match r with | AlwaysF v1 -> AlwaysF (op v1) | DifferentR b -> f b |> DifferentR

        let rec simplify r c =
            let simplifyTwice r1 r2 f = simplify r1 (fun v1 -> simplify r2 (fun v2 -> f v1 v2))
            match r with
            | Real r            -> AlwaysF r |> c
            | Add (r1, r2)       -> simplifyTwice r1 r2 (fun v1 v2 -> compareTwoReals v1 v2 (+) Add |> compareSecondWithComp v1 v2 0.0 |> compareSecondWithComp v2 v1 0.0 |> c)
            | Sub (r1, r2)       -> simplifyTwice r1 r2 (fun v1 v2 -> compareTwoReals v1 v2 (-) Sub |> compareSecondWithComp v1 v2 0.0 |> c)
            | Mul (r1, r2)       -> simplifyTwice r1 r2 (fun v1 v2 -> compareTwoReals v1 v2 (*) Mul |> compareSecondWithComp v1 v2 1.0 |> compareSecondWithComp v2 v1 1.0 |> compareSecondWithComp (AlwaysF 0.0) v2 0.0 |> compareSecondWithComp (AlwaysF 0.0) v1 0.0 |> c)
            | Max (r1, r2)       -> simplifyTwice r1 r2 (fun v1 v2 -> compareTwoReals v1 v2 (fun v1 v2 -> System.Math.Max(v1,v2)) Max |> c)
            | Pow (r1, f)        -> simplify r1 (fun v1-> compareOne v1 (fun v1 -> v1 ^~ f ) (fun v1-> Pow(v1, f)) |> c)
            | _                  -> DifferentR r |> c
            
        simplify r id
        |> toReal
    
    ///<summary>Simplify a Bool</summary>
    let simplifyB b = 
        let toBoolean (b: BoolValue) = match b with | Always b -> Bool b | Different b -> b
        let rec simplify b c =
            let simplifyTwice b1 b2 f = simplify b1 (fun v1 -> simplify b2 (fun v2 -> f v1 v2))
            let insertIfValues b1 b2 bool =
                match b1, b2 with 
                | Always b1, Always b2      -> if b1 = b2 then Always b1 else bool (Bool b1, Bool b2) |> Different
                | Different b1, Always b2   -> bool (b1, Bool b2) |> Different
                | Always b1, Different b2   -> bool (Bool b1, b2) |> Different
                | Different b1, Different b2 -> bool (b1, b2) |> Different

            let compareTwoBools v1 v2 op bool oneAlways c =
                match v1,v2 with
                | Always b1, Always b2      -> Always (op b1 b2) |> c
                | Different b2, Always b1
                | Always b1, Different b2   -> (oneAlways b1 (Different b2)) |> c
                | Different b1, Different b2 -> Different (bool(b1, b2)) |> c
            let compareTwoReals r1 r2 op real c =
                match simplifyR r1, simplifyR r2 with
                | Real r1, Real r2 -> op r1 r2      |> Always |> c
                | r1, r2           -> real (r1,r2)  |> Different |> c
                
            match b with
            | Bool b            -> Always b |> c
            | BAnd(b1,b2)       -> simplifyTwice b1 b2 (fun v1 v2 ->compareTwoBools v1 v2 (&&) BAnd (fun v1 v2 -> if v1 then v2 else Always false) c)
            | BOr(b1,b2)        -> simplifyTwice b1 b2 (fun v1 v2  ->compareTwoBools v1 v2 (||) BOr (fun v1 v2 -> if v1 then Always true else v2) c)
            | BNot(b1)          -> simplify b1 (fun v1 -> match v1 with | Always v -> Always (not v) |> c | Different v -> Different (BNot(v)) |> c )
            | RLT(r1,r2)        -> compareTwoReals r1 r2 (<) RLT c
            | RGT(r1,r2)        -> compareTwoReals r1 r2 (>) RGT c
            | REQ(r1,r2)        -> compareTwoReals r1 r2 (=~) REQ c
            | RLTEQ(r1,r2)      -> compareTwoReals r1 r2 (<=~) RLTEQ c
            | RGTEQ(r1,r2)      -> compareTwoReals r1 r2 (>=~) RGTEQ c
            | BoolIf(b1,b2,b3)  ->
                simplify b1 (fun v1 ->
                    match v1 with 
                    | Always b -> if b then simplify b2 c else simplify b3 c
                    | Different b -> simplifyTwice b2 b3 (fun v2 v3 -> insertIfValues v2 v3 (fun (v2,v3)-> BoolIf(b,v2,v3))  |> c   )
                )
            | CallB (n, args)   ->
                CallB (n, args|> simplifyValueList (fun b -> simplify b id |> toBoolean) id id) |> Different |> c
            | _                 -> Different b |> c


        simplify b id
        |> toBoolean
    
    ///<summary>Simplify a Contract</summary>
    let simplifyC con = 
        let rec simplify con c =  
            let compare2 v1 v2 c = match v1,v2 with | Zero, Zero -> Zero |> c | Zero, v -> v |> c  | v, Zero -> v |> c  | v1, v2 -> And(v1,v2) |> c      
            let IfZeroElseCon v eC c = match v with | Zero -> Zero |> c | _ -> eC |> c  
            match con with
            | Zero                                      -> Zero |> c
            | Pay (curr, value, date, part1, part2)     ->
                Pay (curr, simplifyR value, date, part1, part2) |> c
            | And (con1, con2)                          ->
                simplify con1 (fun v1 -> simplify con2 (fun v2 -> compare2 v1 v2 c ))
            | Scale (con, i)                            -> 
                simplify con (fun v2 ->
                    match v2 with
                    | Scale (v2, i2)                -> Scale (v2, simplifyR (Mul(i, i2))) |> c
                    | Zero           -> Zero |> c
                    | _              -> Scale (v2, simplifyR i) |> c )
            | Shift (con, d)                            ->
                simplify con (fun v2 ->
                    match v2 with
                    | Shift (v2, d2)             -> Shift (v2, d + d2)|> c
                    | Zero           -> Zero |> c
                    | _              -> Shift (v2, d)|> c )
            | If (b, con1, con2)                        ->
                match simplifyB b with
                | Bool b -> if b then simplify con1 c else simplify con2 c
                | b      -> simplify con1 (fun v1 -> simplify con2 (fun v2 -> If(b, v1, v2) |> c))
            | IfUnbound (b, con1)                       ->
                match simplifyB b with
                | Bool b -> if b then simplify con1 c else simplify Zero c
                | b      -> simplify con1 (fun v1 ->  IfUnbound(b, v1) |> c)
            | IfWithin (b, date, con1, con2)            -> 
                match simplifyB b with
                | Bool b -> if b then simplify con1 c else simplify (Shift (con2, date+1)) c
                | b      -> simplify con1 (fun v1 -> simplify con2 (fun v2 -> IfWithin(b, date, v1, v2) |> c))
            | VarC n                                    -> con |> c
            | LetR (n, eRhs, eBody)                     ->
                simplify eBody (fun v2 ->IfZeroElseCon v2 (LetR (n, simplifyR eRhs, v2)) c)
            | LetB (n, eRhs, eBody)                     ->
                simplify eBody (fun v2 ->IfZeroElseCon v2 (LetB (n, simplifyB eRhs, v2)) c)
            | LetC (n, eRhs, eBody)                     ->
                simplify eRhs (fun v1 -> simplify eBody (fun v2 ->IfZeroElseCon v2 (LetC (n, v1, v2)) c))
            | LetFunC(n, args, eRhs, eBody)             ->
                simplify eRhs (fun v1 -> simplify eBody (fun v2 ->IfZeroElseCon v2 (LetFunC(n, args, v1, v2)) c))
            | LetFunB(n, args, eRhs, eBody)             ->
                simplify eBody (fun v2 -> LetFunB(n, args, simplifyB eRhs, v2) |> c)
            | LetFunR(n, args, eRhs, eBody)             ->
                simplify eBody (fun v2 -> LetFunR(n, args, simplifyR eRhs, v2) |> c)
            | IterCon(n, v, i, di)                      -> simplify v (fun v -> IterCon(n, v, simplifyR i, simplifyR di))
            | CallC (n, args)                           ->
                CallC (n, args|> simplifyValueList simplifyB simplifyR (fun c -> simplify c id)) |> c
        simplify con id
        |> removeLetTypesC

