module ContractProperties
    open ContractTypes
    open ContractHelperFunctions
    open ContractEval
    open System
    open MaxValueContractsProperty
    
    
    let loop r1 r2 listInit=
        let mapSet d (l, i) = (l, i+d)
        let addDays set= 
            listInit (fun d -> set |>Set.map (mapSet d) )
            |> List.fold (fun acc v-> v |>Set.fold (fun acc v -> Set.add v acc) acc ) Set.empty
        (addDays r1, addDays r2)

    ///<summary>List of observables from a Real</summary>
    let rec getObservablesFromReal v timeExtend letRealEnv acc c =
        let getObsFV v acc = getObservablesFromReal v timeExtend letRealEnv acc
        match v with 
        | Real _                    -> acc |> c
        | Add (v1, v2)
        | Sub (v1, v2)
        | Max(v1,v2)
        | Mul (v1, v2)              -> getObsFV v1 acc (fun acc -> getObsFV v2 acc c)
        | Pow (v1, _)               -> getObsFV v1 acc c
        | ObsReal (date, label)     -> (fst acc, Set.add (label, addDates date timeExtend) (snd acc)) |> c
        | FoldReal (n,v,ac, i, di)  ->
            let acc = getObsFV ac acc c
            fun (i,di) ->
                let (eBody, letRealEnv) = getMapRealAndAddClosure n [Real 0.0 |> VReal; v|> VReal] letRealEnv
                [0..i] |> List.fold (fun acc t -> getObservablesFromReal eBody (timeExtend + (t * di)) letRealEnv acc id ) acc
            |> matchFoldFailIfNone evalReal i di 
            |> c
        | VarR _                    -> acc |> c
        | CallR (n,args)            ->
            let acc = args |> List.fold (fun acc v -> match v with | VReal r -> getObsFV r acc id | _ -> acc ) acc
            let (eBody, letRealEnv) = getMapRealAndAddClosure n args letRealEnv
            getObservablesFromReal eBody timeExtend letRealEnv acc c
    
    ///<summary>List of observables from a Bool</summary>
    let rec getObservablesFromBool v timeExtend (letBoolEnv:Map<string, LetType<Bool>>) letRealEnv acc c=
        let getObsFB b = getObservablesFromBool b timeExtend letBoolEnv letRealEnv
        let getObsFR r = getObservablesFromReal r timeExtend letRealEnv
        match v with 
        | Bool _                    -> acc
        | BAnd(v1, v2)
        | BOr(v1, v2)               -> getObsFB v1 acc (fun acc -> getObsFB v2 acc c)
        | RLT (v1, v2)
        | RGT (v1, v2)
        | REQ (v1, v2)
        | RLTEQ (v1, v2)
        | RGTEQ (v1, v2)            -> getObsFR v1 acc (fun acc -> getObsFR v2 acc c)
        | BNot(v1)                  -> getObsFB v1 acc c
        | ObsBool (date, label)     -> (Set.add (label, addDates date timeExtend) (fst acc), snd acc) |> c
        | BoolIf (v1, v2, v3)       -> getObsFB v1 acc (fun acc -> getObsFB v2 acc (fun acc -> getObsFB v3 acc c))
        | FoldBool(n,v, ac, i, di)        ->
            let acc = getObsFB ac acc c
            fun (i,di) ->
                let (eBody, (letBoolEnv, letRealEnv)) = getMapBoolAndAddClosure n [Bool true |> VBool; v |> VBool] letBoolEnv
                let r1, r2 = getObservablesFromBool eBody timeExtend letBoolEnv letRealEnv acc id
                loop r1 r2 (fun f -> [0..di..(di*i)] |> List.map f)
            |> matchFoldFailIfNone evalReal i di
            |> c

        | VarB _                    -> acc |> c
        | CallB (n,args)            ->
            let acc = args |> List.fold (fun acc v -> match v with | VBool b -> getObsFB b acc id | VReal r -> getObsFR r acc id | _ -> acc ) acc
            let (eBody, (letBoolEnv, letRealEnv)) = getMapBoolAndAddClosure n args letBoolEnv
            getObservablesFromBool eBody timeExtend letBoolEnv letRealEnv acc c
    
    ///<summary>Set of observables from a Contract</summary>
    let setOfObservables c =
        let rec aux con timeExtend letBoolEnv letRealEnv letConEnv acc c=
            let auxNewc con acc c= aux con timeExtend letBoolEnv letRealEnv letConEnv acc c
            let getObservablesFromBool b = getObservablesFromBool b timeExtend letBoolEnv  letRealEnv
            let getObservablesFromReal r = getObservablesFromReal r timeExtend letRealEnv
            match con with
            | Zero                              -> acc |> c
            | Pay (_, value, _, _, _)           -> getObservablesFromReal value acc c
            | And (con1, con2)                  -> auxNewc con1 acc (fun acc -> auxNewc con2 acc c)
            | Scale (con, i)                    -> auxNewc con acc c 
            | Shift (con, d)                    -> aux con (addDates d timeExtend) letBoolEnv letRealEnv letConEnv acc c
            | If (obs, con1, con2)              -> getObservablesFromBool obs acc (fun acc -> auxNewc con1 acc (fun acc ->auxNewc con2 acc c))
            | IfUnbound (obs, con1)  ->
                let listFunc time con acc = getObservablesFromBool obs acc (fun acc -> aux con time letBoolEnv letRealEnv letConEnv acc id)
                let r1, r2 = listFunc timeExtend con1 acc
                loop r1 r2 (List.init (unboundHorizonDays+1))
                |> c
            | IfWithin (obs, date, con1, con2)  ->
                let listFunc time con acc = getObservablesFromBool obs acc (fun acc -> aux con time letBoolEnv letRealEnv letConEnv acc id)
                let r1, r2 = listFunc timeExtend con1 acc
                loop r1 r2 (List.init (unboundHorizonDays+1))
                |> listFunc (timeExtend + date + 1) con2
                |> c
            | VarC n                            -> auxNewc (getLetVariable n letConEnv "contract") acc c
            | LetR (n, eRhs, eBody)             -> getObservablesFromReal eRhs acc (fun acc -> auxNewc eBody acc c)  //todo add n
            | LetB (n, eRhs, eBody)             -> getObservablesFromBool eRhs acc (fun acc -> auxNewc eBody acc c)  //todo add n
            | LetC (n, eRhs, eBody)             -> auxNewc eRhs acc (fun acc -> aux eBody timeExtend letBoolEnv letRealEnv (Map.add n (Variable eRhs) letConEnv) acc c)
            | LetFunC(n, args, eRhs, eBody)     -> 
                let closurec = LetFunCToClosure args eRhs letBoolEnv letRealEnv letConEnv 
                aux eBody timeExtend letBoolEnv letRealEnv (Map.add n closurec letConEnv) acc c
            | LetFunB(n, args, eRhs, eBody)     -> 
                let closureb = LetFunBToClosure args eRhs letBoolEnv letRealEnv
                aux eBody timeExtend (Map.add n closureb letBoolEnv) letRealEnv letConEnv acc c
            | LetFunR(n, args, eRhs, eBody)     -> 
                let closurer = LetFunRToClosure args eRhs letRealEnv
                aux eBody timeExtend letBoolEnv (Map.add n closurer letRealEnv) letConEnv acc c
            | IterCon(n, v, i, di)              ->
                fun (i,di) ->
                    let (eBody, (letBoolEnv, letRealEnv, letConEnv)) = getMapContractAndAddClosure n [v|> VCon] letConEnv
                    [0..i] |> List.fold (fun acc t -> aux eBody (timeExtend + (t * di)) letBoolEnv letRealEnv letConEnv acc id ) acc
                |> matchFoldFailIfNone evalReal i di 
                |> c

            | CallC (n,args)                    ->
                let acc = args |> List.fold (fun acc v -> match v with | VBool b -> getObservablesFromBool b acc id | VReal r -> getObservablesFromReal r acc id | VCon c -> auxNewc c acc id) acc
                let (eBody, (_, _, letConEnv)) = getMapContractAndAddClosure n args letConEnv
                aux eBody timeExtend letBoolEnv letRealEnv letConEnv acc c
                
        aux c 0 Map.empty Map.empty Map.empty (Set.empty, Set.empty) id
    (*
    let allCombinationOfProperties c =
        let rec aux acc lst =
            match lst with
            | [] -> acc
            | h::t ->
                let next =
                    [h]
                    ::List.map (fun el -> h::el) acc
                    @ acc
                aux next t
        let s1,s2 = setOfObservables c
        (aux [] s1, aux [] s2)
    
    let ContractsHaveAlwaysSameValeu c1 c2 =
        let comb1, comb2 = allCombinationOfProperties c1
        let rec aux com1 com2 acc =
            match com1, com2 with
            | [], _ -> acc
            | h::t, []  ->
                let realEnv = Map.empty
                let boolEnv = h |> List.map (fun (l,d)-> ((d,l),true)) |> Map.ofList
                let temp = eval c1 boolEnv realEnv = eval c2 boolEnv realEnv
                printfn "combinationx: %A" temp
                if temp then aux t com2  acc else false
            | h::t, h2::t2  -> 
                let realEnv = h2 |> List.map (fun (l,d)-> ((d,l),10.0)) |> Map.ofList
                let boolEnv = h |> List.map (fun (l,d)-> ((d,l),true)) |> Map.ofList
                let temp = eval c1 boolEnv realEnv = eval c2 boolEnv realEnv
                printfn "combinationx: %A" temp
                if temp then aux t t2 (temp && acc) else false
                
        aux comb1 comb2 true
    *)
    
    ///<summary>Set of parties from a Contract</summary>
    let setOfParties c =
        let rec aux con timeExtend letBoolEnv letRealEnv letConEnv acc c =
            let rec addPartyToSet acc (l,_) =
                match l with
                | Action _ 
                | Business _        -> acc
                | Defaults p
                | Exercises p       -> acc |> Set.add p 
                | Pickable (l, _)   -> (l,0) |> addPartyToSet acc

            let setMapLableToPary (s1, s2) =
                Set.union s1 s2
                |> Set.fold addPartyToSet Set.empty

            let unionSetAndAcc s acc     = s |> setMapLableToPary |> Set.union acc
            let getObservablesFromReal v = getObservablesFromReal v timeExtend letRealEnv (Set.empty, Set.empty) id |> unionSetAndAcc
            let getObservablesFromBool v = getObservablesFromBool v timeExtend letBoolEnv letRealEnv (Set.empty, Set.empty) id |> unionSetAndAcc
            let auxNewC con = aux con timeExtend letBoolEnv letRealEnv letConEnv
            match con with
            | Zero                              -> acc |> c
            | Pay (_, value, _, p1, p2)         -> acc |> (Set.add (p1) >> Set.add (p2) >> getObservablesFromReal value) |> c
            | And (con1, con2)                  -> auxNewC con1 acc (fun acc -> auxNewC con2 acc c)
            | Scale (con, i)                    -> auxNewC con acc c
            | Shift (con, d)                    -> aux con (addDates d timeExtend) letBoolEnv letRealEnv letConEnv acc c
            | If (obs, con1, con2)
            | IfWithin (obs, _, con1, con2)     -> auxNewC con1 (acc |> getObservablesFromBool obs) (fun acc -> auxNewC con2 acc c)
            | IfUnbound (obs, con1)             -> auxNewC con1 (acc |> getObservablesFromBool obs) c
            | VarC _                            -> acc |> c
            | LetR(n, eRhs, eBody)              -> auxNewC eBody (acc |> getObservablesFromReal eRhs) c   //todo add n
            | LetB(n, eRhs, eBody)              -> auxNewC eBody (acc |> getObservablesFromBool eRhs) c   //todo add n
            | LetC(n, eRhs, eBody)              -> auxNewC eRhs acc (fun acc -> auxNewC eBody acc c)      //todo add n
            | LetFunC(n, args, eRhs, eBody)     ->
                let closurec = LetFunCToClosure args eRhs letBoolEnv letRealEnv letConEnv 
                aux eBody timeExtend  letBoolEnv letRealEnv (Map.add n (closurec) letConEnv) acc c
            | LetFunB(n, args, eRhs, eBody)     ->
                let closureb = LetFunBToClosure args eRhs letBoolEnv letRealEnv 
                aux eBody timeExtend  (Map.add n (closureb) letBoolEnv) letRealEnv letConEnv acc c
            | LetFunR(n, args, eRhs, eBody)     ->
                let closurer = LetFunRToClosure args eRhs letRealEnv 
                aux eBody timeExtend  letBoolEnv (Map.add n (closurer) letRealEnv) letConEnv acc c
            | IterCon(n,v,i,di)                 -> auxNewC v acc (getObservablesFromReal i >> getObservablesFromReal i >> getObservablesFromReal di)    //todo get parties from n
            | CallC (n, args)                   -> args |> List.fold (fun acc v -> match v with | VCon c -> auxNewC c acc id | _ -> acc ) acc           //todo get parties from n
        aux c 0 Map.empty Map.empty Map.empty Set.empty id

    
    
    ///<summary>Helper function mapping contract</summary>
    let mapContract con func c = 
        let match1 con1 f =
            func con1 (fun v1 -> f v1)
        let match2 con1 con2 f =
            func con1 (fun v1 -> func con2 (fun v2 ->  f (v1, v2)))
        match con with
            | And (con1, con2)                  -> match2 con1 con2 (And>>c)
            | Scale (c1, i)                     -> func c1 (fun v1 -> Scale (v1 , i) |> c)
            | Shift (c1, d)                     -> match1 c1 (fun v -> Shift (v, d) |> c)
            | If (v, c1, c2)                    -> match2 c1 c2 (fun (v1,v2) -> If (v, v1, v2) |> c)
            | IfWithin (b, d, c1, c2)           -> match2 c1 c2 (fun (v1,v2) -> IfWithin (b, d, v1, v2) |> c)
            | IfUnbound (b,c1)                  -> match1 c1 (fun v -> IfUnbound (b, v) |> c)
            | LetB(n, b, c1)                    -> match1 c1 (fun v ->  LetB(n, b, v) |> c)
            | LetR(n, r, c1)                    -> match1 c1 (fun v ->  LetR(n, r, v) |> c)
            | LetC(n, c1, c2)                   -> match2 c1 c2 (fun (v1,v2) -> LetC(n, v1, v2) |> c)
            | LetFunB(n, args, b, c1)           -> match1 c1 (fun v ->  LetFunB(n, args, b, v) |> c)
            | LetFunR(n, args, r, c1)           -> match1 c1 (fun v ->  LetFunR(n, args, r, v) |> c)
            | LetFunC(n, args, c1, c2)          -> match2 c1 c2 (fun (v1,v2) -> LetFunC(n, args, v1, v2) |> c)
            | VarC(_)
            | CallC(_,_)
            | Zero
            | IterCon(_,_,_,_)
            | Pay (_, _, _, _, _)               -> con |> c


    ///<summary>Generate a contract with pay negative</summary>
    let genNegateValueContract con =
        let rec getContract con c =
            match con with
                | Pay (curr, value, date, part1, part2)     -> Pay (curr, Sub(Real 0.0, value), date, part1, part2) |> c
                | _ -> mapContract con getContract c
        getContract con id
        
    ///<summary>Generate a contract with parties paying reversed</summary>
    let genNegatePartyContract con =
        let rec getContract con c =
            match con with
                | Pay (curr, value, date, part1, part2)     ->
                    Pay (curr, value, date, part2, part1) |> c
                | _ -> mapContract con getContract c
        getContract con id
    
    ///<summary>Generate a contract with ands and If reversed</summary>
    let genSwitchedContract con =
        let rec getContract con c =
            match con with
                | And (con1, con2)            -> mapContract con1 getContract (fun v1 -> mapContract con2 getContract (fun v2 -> And (v2, v1) |> c))
                | If (v, con1, con2)          -> mapContract con1 getContract (fun v1 -> mapContract con2 getContract (fun v2 -> If (BNot v, v2, v1) |> c))
                | _ -> mapContract con getContract c
        getContract con id




    ///<summary>Property that contracts have same parties</summary>
    let equalParties c1 c2 = 
        let parties1, parties2 = setOfParties c1, setOfParties c2
        Set.difference parties1 parties2 |> Set.isEmpty
    
    ///<summary>Property that contracts have same max value</summary>
    let equalMaxValue currencyExchangeValue c1 c2 = 
        let parties1, parties2 = setOfParties c1, setOfParties c2
        (Set.union parties1 parties2) |> foldMaxValue c1 c2 currencyExchangeValue true

    ///<summary>Property that contracts have same observables, -warning: slow, large set easily returned</summary>
    let equalSetOfObservables c1 c2 = 
        let setReal1, setBool1 = setOfObservables c1
        let setReal2, setBool2 = setOfObservables c2
        Set.difference setReal1 setReal2 |> Set.isEmpty 
        >>= (fun _ -> (Set.difference setBool1 setBool2 |> Set.isEmpty))
