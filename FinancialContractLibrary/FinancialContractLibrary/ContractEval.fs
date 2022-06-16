module ContractEval
    open System
    open ContractTypes
    open ContractSimplify
    open ContractHelperFunctions

    
    ///<summary>If count set is less than 0 then None, else update count and return Some v </summary>
    let updateCountAndRet obsEnv v = 
        match obsEnv.count with
        | None -> Some v
        | Some c when c<0 -> None
        | Some c ->
            obsEnv.count <- Some (c-1);
            Some v

    let addRealToObs key obsEnv v =
        obsEnv.realObsEnv <- obsEnv.realObsEnv |> Map.add key v;
        updateCountAndRet obsEnv v
    let addBoolToObs key obsEnv v =
        obsEnv.boolObsEnv <- obsEnv.boolObsEnv |> Map.add key v;
        updateCountAndRet obsEnv v

    ///<summary>Add to obsEnv the key mapped to a random float, and handle if count <=0 </summary>
    let generateRealObs key obsEnv = 
        ((float((new System.Random ()).Next (0, 1000))) / 10.0)
        |> addRealToObs key obsEnv
    ///<summary>Add to obsEnv the key mapped to a random bool, and handle if count <=0 </summary>
    let generateBoolObs key obsEnv = 
        (new System.Random ()).Next (1000) |> (<) 500
        |> addBoolToObs key obsEnv
        
    ///<summary>Add to obsEnv the key mapped to a float from console</summary>
    let rec generateFloatObsFromConsole key obsEnv = 
        printfn "Need float for: %A"  key
        (System.Console.ReadLine()).ToLower().Trim() 
        |> fun v -> try v |> float |> addRealToObs key obsEnv with | _ -> generateFloatObsFromConsole key obsEnv

    ///<summary>Add to obsEnv the key mapped to a "true" or "false" from console</summary>
    let rec generateBoolObsFromConsole key obsEnv = 
        printfn "Need {true,false} for: %A"  key
        (System.Console.ReadLine()).ToLower().Trim() 
        |> function 
        | "true"  -> addBoolToObs key obsEnv true
        | "false" -> addBoolToObs key obsEnv false
        | _      -> generateBoolObsFromConsole key obsEnv


    let toInt (v: float) = Convert.ToInt32(Math.Round(v))
    
    let matchTwoOptions v1 v2 op= match v1, v2 with | None,_ |_, None -> None | Some v1, Some v2 -> op v1 v2 |> Some
    let matchOneOptions v1 op= match v1 with | None -> None | Some v1 -> op v1 |> Some
    let matchOneOpRetOption v1 op= match v1 with | None -> None | Some v1 -> op v1
    let matchFold evalAcc acc accToVal timeExtend v c getMap env eval = 
        function
        | Some i, Some di -> 
            let i,di = toInt i, toInt di
            fun acc ->
                let func acc t = 
                    fun acc -> 
                        let (eBody, envs) = getMap [acc |> accToVal; v] env
                        eval eBody (timeExtend + (t*di)) envs
                    |> matchOneOpRetOption acc
                [0..(Math.Max(0,(i-1)))] |> List.fold func acc|> c
            |> evalAcc acc
        | _ -> None |> c
    let matchFoldFailIfNone evalReal i di op =
        let f = fun r -> evalReal r 0 (emptyObsEnv ()) Map.empty generateRealObs
        match f i, f di with
        | Some i, Some di -> op (i|> toInt, di|>toInt)
        | _ -> failwith "shouldn't happen"
    let removeIfPressent n map =
        match map |> Map.tryFind n with
        | Some (Variable _) -> Map.remove n map
        | _ -> map
    let replaceVarC con oldEnvironment=
        let rec aux con oldEnvironment c = 
            match con with
                | Zero
                | Pay _                                     -> con |> c
                | And (con1, con2)                          -> aux con1 oldEnvironment (fun v1 -> aux con2 oldEnvironment (fun v2 -> And (v1,v2) |> c))
                | Scale (con1, i)                           -> aux con1 oldEnvironment (fun v1 -> Scale (v1, i) |> c)
                | Shift (con1, d)                           -> aux con1 oldEnvironment (fun v1 -> Shift (v1, d) |> c)
                | If (b, con1, con2)                        -> aux con1 oldEnvironment (fun v1 -> aux con2 oldEnvironment (fun v2 -> If (b, v1,v2) |> c))
                | IfUnbound (b, con1)                       -> aux con1 oldEnvironment (fun v1 -> IfUnbound (b, v1) |> c)
                | IfWithin (b, date, con1, con2)            -> aux con1 oldEnvironment (fun v1 -> aux con2 oldEnvironment (fun v2 -> IfWithin (b, date, v1,v2) |> c))
                | LetR (n, eRhs, eBody)                     -> aux eBody oldEnvironment (fun v2 -> LetR (n, eRhs, v2) |> c)
                | LetB (n, eRhs, eBody)                     -> aux eBody oldEnvironment (fun v2 -> LetB (n, eRhs, v2) |> c)
                | LetC (n, eRhs, eBody)                     -> aux eRhs oldEnvironment (fun v1 -> aux eBody (removeIfPressent n oldEnvironment) (fun v2 -> LetC (n, v1, v2) |> c))
                | LetFunB(n, args, eRhs, eBody)             -> aux eBody oldEnvironment (fun v2 -> LetFunB(n, args, eRhs, v2) |> c)
                | LetFunR(n, args, eRhs, eBody)             -> aux eBody oldEnvironment (fun v2 -> LetFunR(n, args, eRhs, v2) |> c)
                | LetFunC(n, args, eRhs, eBody)             -> aux eRhs oldEnvironment (fun v1 -> aux eBody (removeIfPressent n oldEnvironment) (fun v2 -> LetFunC(n, args, v1, v2) |> c))
                | IterCon(n, v, i, di)                      -> aux v oldEnvironment (fun v -> IterCon(n, v, i, di) |> c)
                | VarC n                                    -> 
                    match oldEnvironment |> Map.tryFind n with
                    | Some (Variable eRhs) -> eRhs |> c
                    | _ -> con |> c
                | CallC (n, args)                           ->
                    args 
                    |> List.map (fun v -> match v with VCon c -> aux c oldEnvironment id |> VCon | _ -> v)
                    |> fun args -> CallC (n, args) |> c
        aux con oldEnvironment id
    
    ///<summary>Evaluate a Real, return option, some result or None if obsEnv count<0 </summary>
    let evalReal v timeExtend obsEnv letRealEnv genObsReal =
        let rec aux v timeExtend letRealEnv c= 
            let auxNewVT v t = aux v t (letRealEnv:Map<string, LetType<Real>>) 
            let auxNewV v = auxNewVT v timeExtend
            let unpackAndCompare v1 v2 op =  auxNewV v1 (fun v1 -> auxNewV v2 (fun v2 -> matchTwoOptions v1 v2 op |> c))
            let unpac1 v1 op = auxNewV v1 (fun v1 -> matchOneOptions v1 op |> c)
            match v with
            | Real r                    -> Some r |> c
            | Add (v1, v2)              -> unpackAndCompare v1 v2 (+) 
            | Sub (v1, v2)              -> unpackAndCompare v1 v2 (-) 
            | Mul (v1, v2)              -> unpackAndCompare v1 v2 (*) 
            | Max (v1, v2)              -> unpackAndCompare v1 v2 (fun v1 v2 -> Math.Max(v1,v2)) 
            | Pow (v1, f)               -> unpac1 v1 (fun x -> x ^~ f)
            | ObsReal (date, label)     -> 
                match obsEnv.realObsEnv |> Map.tryFind (addDates date timeExtend, label)  with
                | None   -> genObsReal (addDates date timeExtend, label) obsEnv |> c
                | Some v -> Some v   |> c
            | FoldReal (n,v,acc, i, di)      -> 
                auxNewV i (fun i -> auxNewV di (fun di ->
                    let func =
                        (fun eBody t letRealEnv -> aux eBody t letRealEnv id)
                        |> matchFold auxNewV acc (Real >> VReal) timeExtend (VReal v) c (getMapRealAndAddClosure n) letRealEnv
                    func (i, di)
                ))
            | VarR n               -> auxNewV (getLetVariable n letRealEnv "real") (fun v -> v |> c) 
            | CallR (n, args)                           ->
                let currentClosure = getLetClosure n letRealEnv "real" |> Closure
                let evaluatedArgs =  args|> mapArg (fun _ ->Some false) (fun r -> auxNewV r id ) (fun _ ->Some Zero)
                match evaluatedArgs with
                | None -> None
                | Some evaluatedArgs ->
                    let (eBody, letRealEnv) = getMapRealAndAddClosure n evaluatedArgs letRealEnv
                    aux eBody timeExtend (Map.add n currentClosure letRealEnv) (fun v1 -> v1 |> c)
        aux v timeExtend letRealEnv id
    
    ///<summary>Evaluate a Bool, return option, some result or None if obsEnv count<0 </summary>
    let evalBool v timeExtend obsEnv (letBoolEnv:Map<string, LetType<Bool>>) (letRealEnv:Map<string, LetType<Real>>) genObsReal genObsBool=
        let rec eval v timeExtend letBoolEnv letRealEnv c = 
            let evalNewV v = eval v timeExtend letBoolEnv letRealEnv
            let unpackAndCompare v1 v2 op       =  evalNewV v1 (fun v1 -> evalNewV v2 (fun v2 -> matchTwoOptions v1 v2 op |> c))
            let evalReal r = evalReal r timeExtend obsEnv letRealEnv genObsReal
            let unpackAndCompareFloat v1 v2 op  =  matchTwoOptions (evalReal v1) (evalReal v2) op |> c
            match v with
            | Bool b                    -> b |> Some |> c
            | BAnd(v1, v2)              -> unpackAndCompare v1 v2 (&&)
            | BOr(v1, v2)               -> unpackAndCompare v1 v2 (||)
            | BNot(v)                   -> evalNewV v (fun v -> matchOneOptions v not |> c) 
            | RLT (v1, v2)              -> unpackAndCompareFloat v1 v2 (<)   
            | RGT (v1, v2)              -> unpackAndCompareFloat v1 v2 (>)  
            | REQ (v1, v2)              -> unpackAndCompareFloat v1 v2 (=~)  
            | RLTEQ (v1, v2)            -> unpackAndCompareFloat v1 v2 (<=~)
            | RGTEQ (v1, v2)            -> unpackAndCompareFloat v1 v2 (>=~) 
            | ObsBool (date, label)     -> 
                match obsEnv.boolObsEnv |> Map.tryFind (addDates date timeExtend,label) with 
                | None      -> genObsBool (addDates date timeExtend, label) obsEnv |> c
                | Some v    -> Some v |> c
            | BoolIf (v1, v2, v3)        -> 
                (fun v1 -> matchOneOpRetOption v1 (fun v1 -> evalNewV (if v1 then v2 else v3) c))
                |> eval v1 timeExtend letBoolEnv letRealEnv 
            | FoldBool (n, v, acc, i, di)      -> 
                let func =
                    (fun eBody t (letBoolEnv, letRealEnv) -> eval eBody t letBoolEnv letRealEnv id)
                    |> matchFold evalNewV acc (Bool >> VBool) timeExtend (VBool v) c (getMapBoolAndAddClosure n) letBoolEnv
                func (evalReal i, evalReal di)
            | VarB n               -> evalNewV (getLetVariable n letBoolEnv "bool") (fun v1-> v1 |> c) 
            | CallB (n, args)                           ->
                let currentClosure = getLetClosure n letBoolEnv "bool" |> Closure
                let evaluatedArgs = 
                    args
                    |> mapArg (fun b -> evalNewV b id) (fun r -> evalReal r) (fun _ -> Some Zero)
                match evaluatedArgs with 
                | None -> None 
                | Some evaluatedArgs ->
                    let (eBody, (letBoolEnv, letRealEnv)) = getMapBoolAndAddClosure n evaluatedArgs letBoolEnv
                    eval eBody timeExtend (Map.add n currentClosure letBoolEnv) letRealEnv (fun v1 -> v1 |> c)
        eval v timeExtend letBoolEnv letRealEnv id
    
    
    ///<summary>Helperfunction for adding a Pay to one of the transaction types </summary>
    let mapAddToList time (part1, part2, value, curr) map =
        let trans = (part1, part2, value, curr)
        let addToMap map key f= 
            match Map.tryFind key map with
            | Some lst -> (f trans) :: lst
            | None     -> [f trans]
            |> (fun v -> map |> Map.add key v)
        match map with
        | TransactionsMapDay map -> 
            addToMap map time id |> TransactionsMapDay
        | TransactionsMapParty (map1, map2) ->
            let addPartToMap part map = addToMap map part (fun trans -> (time,trans))
            (addPartToMap part1 map1, addPartToMap part2 map2) |> TransactionsMapParty

    
    ///<summary>Evaluate a Contract, return option, some result or None if obsEnv count<0 </summary>
    let evalConFromT c t obsEnv transactionsMap genObsReal genObsBool = 
        let ifw d date v con1 con2 evalConWithNewT evalBool c acc =
            let maxDay = addDates date d
            let rec aux d =
                if d > maxDay then evalConWithNewT con2 d acc c
                else 
                    match evalBool v d with | None -> None | Some b ->  if b then evalConWithNewT con1 d acc c else aux (d+1)
            aux d 
        let rec eval con scale timeExtend (letBoolEnv:Map<string, LetType<Bool>>) (letRealEnv:Map<string, LetType<Real>>) (letConEnv:Map<string, LetType<Contract>>) acc c=
            let evalConWithNewT con t acc c= eval con scale t letBoolEnv letRealEnv letConEnv acc c
            let evalWithNewCon c = evalConWithNewT c timeExtend

            let evalReal r = evalReal r timeExtend obsEnv letRealEnv genObsReal

            let evalBool b t = evalBool b t obsEnv letBoolEnv letRealEnv genObsReal genObsBool
            match con with
            | Zero                  -> acc |> c
            | Pay (curr, value, date, part1, part2) ->
                match acc, (evalReal value) with
                | Some acc, Some v ->
                    acc |> mapAddToList (addDates date timeExtend)  (part1, part2, v * scale, curr) |> Some |> c
                | _ -> None |> c
            | And (con1, con2)      -> evalWithNewCon con1 acc (fun acc -> evalWithNewCon con2 acc c)
            | Scale (con, i)        ->
                matchOneOpRetOption (evalReal i) (fun v -> eval con (scale * v) timeExtend letBoolEnv letRealEnv letConEnv acc c)
            | Shift (con, d)        -> evalConWithNewT con (addDates d timeExtend) acc c
            | If (v, con1, con2)    ->
                fun b -> evalWithNewCon (if b then con1 else con2) acc c
                |> matchOneOpRetOption (evalBool v timeExtend)
            | IfUnbound (v, con)                        ->
                acc |> ifw timeExtend unboundHorizonDays v con Zero evalConWithNewT evalBool c
            | IfWithin (v, date, con1, con2)            ->
                acc |> ifw timeExtend date v con1 con2 evalConWithNewT evalBool c
            | LetR (n, eRhs, eBody)                     ->
                matchOneOpRetOption (evalReal eRhs) (fun r -> eval eBody scale timeExtend letBoolEnv (Map.add n (r |> Real |> Variable) letRealEnv) letConEnv acc c)
            | LetB (n, eRhs, eBody)                     ->
                matchOneOpRetOption (evalBool eRhs timeExtend) (fun b ->eval eBody scale timeExtend (Map.add n (b |> Bool |> Variable) letBoolEnv) letRealEnv letConEnv acc c)
            | LetC (n, eRhs, eBody)                     ->
                 eval eBody scale timeExtend letBoolEnv letRealEnv (Map.add n (replaceVarC eRhs letConEnv |> Variable) letConEnv) acc c
            | LetFunC(n, args, eRhs, eBody)             ->
                let closurec = LetFunCToClosure args eRhs letBoolEnv letRealEnv letConEnv 
                eval eBody scale timeExtend letBoolEnv letRealEnv (Map.add n (closurec) letConEnv) acc c
            | LetFunB(n, args, eRhs, eBody)             ->
                let closureb = LetFunBToClosure args eRhs letBoolEnv letRealEnv 
                eval eBody scale timeExtend (Map.add n (closureb) letBoolEnv) letRealEnv letConEnv acc c
            | LetFunR(n, args, eRhs, eBody)             ->
                let closurer = LetFunRToClosure args eRhs letRealEnv 
                eval eBody scale timeExtend letBoolEnv (Map.add n (closurer) letRealEnv) letConEnv acc c
            | VarC n                                    -> 
                evalWithNewCon (getLetVariable n letConEnv "contract") acc c
            | IterCon(n,v,i,di)                 ->
                let currentClosure  = getLetClosure n letConEnv "contract" |> Closure
                let evaluatedArgs   = [replaceVarC v letConEnv |> VCon]
                let (eBody, (letBoolEnv, letRealEnv, letConEnv)) = getMapContractAndAddClosure n evaluatedArgs letConEnv
                let letConEnv       = Map.add n currentClosure letConEnv
                match evalReal i, evalReal di with
                | Some i, Some di ->
                    let i,di = toInt i, toInt di
                    let result = 
                        [0..(Math.Max(0,(i-1)))] 
                        |> List.map (fun t -> timeExtend + (t*di))
                        |> List.fold (fun c' t -> c' << fun acc -> eval eBody scale t letBoolEnv letRealEnv letConEnv acc id ) c
                    result acc
                | _               -> None
            | CallC (n, args)                           ->
                let currentClosure = getLetClosure n letConEnv "contract" |> Closure
                let evaluatedArgs = 
                    args |> mapArg (fun b -> evalBool b timeExtend) (fun r -> evalReal r) (fun c -> replaceVarC c letConEnv |> Some)
                match evaluatedArgs with
                | None ->None
                | Some evaluatedArgs->
                    let (eBody, (letBoolEnv, letRealEnv, letConEnv)) = 
                        getMapContractAndAddClosure n evaluatedArgs letConEnv
                    eval eBody scale timeExtend letBoolEnv letRealEnv (Map.add n currentClosure letConEnv) acc c
        let sortMap m = m |> Map.toList |> List.sortBy (fst)
        eval c 1.0 t Map.empty Map.empty Map.empty (Some transactionsMap) id
        |> function
           | None -> None
           | Some (TransactionsMapDay m)           -> m |> sortMap |> TransactionsDay |> Some
           | Some (TransactionsMapParty (m1,m2))   -> (m1 |> sortMap, m2 |> sortMap) |> TransactionsParty |> Some

    let evalFromTMapDay c t obsEnv   = evalConFromT c t obsEnv (TransactionsMapDay Map.empty)               generateRealObs generateBoolObs
    let evalFromTMapParty c t obsEnv = evalConFromT c t obsEnv (TransactionsMapParty (Map.empty,Map.empty)) generateRealObs generateBoolObs
    let eval c obsEnv = evalFromTMapDay c 0 obsEnv
    let evalMapParty c obsEnv = evalFromTMapParty c 0 obsEnv







    
    ///<summary>Generate obsEnv with potentially observables to evaluate a Real </summary>
    let generateRealEnv v timeExtend letRealEnv obsEnv =
        let rec aux v timeExtend (letRealEnv: Map<string, LetType<Real>>) () = 
            let auxNewR r = aux r timeExtend letRealEnv
            match v with
            | Real r                    -> ()
            | Add (v1, v2)
            | Sub (v1, v2)
            | Max (v1,v2)
            | Mul (v1, v2)              -> ()  |> (auxNewR v1 >> auxNewR v2)
            | Pow (v1, f)               -> () |> auxNewR v1
            | ObsReal (date, label)     -> 
                let key = (addDates date timeExtend, label)
                match obsEnv.realObsEnv |> Map.tryFind key  with
                | None   -> generateRealObs key obsEnv |> ignore
                | Some v -> ()
            | FoldReal(n, v, acc, i, di)        -> 
                fun (i,di) ->
                    let evaluatedArgs =  [0.0 |> Real |> VReal ; v|> VReal]
                    let (eBody, letRealEnv) = getMapRealAndAddClosure n evaluatedArgs letRealEnv
                    let func t = () |> aux eBody (timeExtend + (t*di)) letRealEnv
                    [0..(i-1)] |> List.iter func
                |> matchFoldFailIfNone evalReal i di 

            | VarR n                     -> ()
            | CallR(n, args)             ->
                args  |> List.iter (fun v -> match v with | VReal r -> auxNewR r ()  | _ -> ()    )
                
                let (eBody, letRealEnv) = getMapRealAndAddClosure n args letRealEnv
                () |> aux eBody timeExtend letRealEnv
        aux v timeExtend letRealEnv 

    
    ///<summary>Generate obsEnv with potentially observables to evaluate a Bool </summary>
    let generateEnvFromBool v timeExtend letBoolEnv letRealEnv obsEnv =
        let rec aux v timeExtend letBoolEnv letRealEnv () = 
            let auxNewB b = aux b timeExtend letBoolEnv letRealEnv 
            let generateEnvFromReal r = generateRealEnv r timeExtend letRealEnv obsEnv
            match v with
            | Bool b                    -> ()
            | BAnd(v1, v2)
            | BOr(v1, v2)               -> () |> (auxNewB v1 >> auxNewB v2)
            | BNot(v)                   -> () |> auxNewB v
            | RLT (v1, v2)
            | RGT (v1, v2)
            | REQ (v1, v2)
            | RLTEQ (v1, v2)
            | RGTEQ (v1, v2)            -> () |> (generateEnvFromReal v1 >> generateEnvFromReal v2)
            | ObsBool (date, label)     -> 
                let key = (addDates date timeExtend,label)
                match obsEnv.boolObsEnv |> Map.tryFind key with 
                | None      -> generateBoolObs key obsEnv |> ignore |> ignore
                | Some v    -> ()
            | BoolIf (v1, v2, v3)        -> () |> (auxNewB v1 >> auxNewB v2 >> auxNewB v3)
            | FoldBool(n,v, acc, i, di)         -> 
                fun (i,di) ->
                    let evaluatedArgs =  [true |> Bool |> VBool;  v|> VBool]
                    let (eBody, (letBoolEnv, letRealEnv)) = getMapBoolAndAddClosure n evaluatedArgs letBoolEnv
                    [0..(i-1)] |> List.iter (fun t -> ()|> aux eBody (timeExtend + (t*di)) letBoolEnv letRealEnv)
                |> matchFoldFailIfNone evalReal i di 
            | VarB _                      -> ()
            | CallB(n, args)              ->
                let (eBody, (letBoolEnv, letRealEnv)) = getMapBoolAndAddClosure n args letBoolEnv
                args
                |> List.iter (fun v -> match v with | VCon c -> () | VBool b -> auxNewB b () | VReal r -> generateEnvFromReal r ()   )
                |> aux eBody timeExtend letBoolEnv letRealEnv
        aux v timeExtend letBoolEnv letRealEnv ()

///<summary>Generate obsEnv with potentially observables to evaluate a Contract </summary>
    let generateEnvs c t obsEnv = 
        let rec aux c timeExtend letBoolEnv letRealEnv letConEnv () =
            let auxNewCT c t    = aux c t letBoolEnv letRealEnv letConEnv
            let auxNewC c       = auxNewCT c timeExtend
            let generateEnvFromBoolT b t () = generateEnvFromBool b t letBoolEnv letRealEnv obsEnv
            let generateEnvFromBool b       = generateEnvFromBoolT b timeExtend
            let generateEnvFromReal r       = generateRealEnv r timeExtend letRealEnv obsEnv

            match c with
            | Zero                      -> ()
            | Pay (_, value, _, _, _)   -> () |> generateEnvFromReal value
            | And (con1, con2)          -> () |>(auxNewC con1 >> auxNewC con2)
            | Scale (con, i)            -> () |> auxNewC con
            | Shift (con, d)            -> () |> auxNewCT con (timeExtend+d)
            | If (v, con1, con2)        -> () |> (generateEnvFromBool v >> auxNewC con1 >> auxNewC con2)
            | IfUnbound (v, con)        -> 
                listFromNotToMax timeExtend
                |> List.iter (fun t ->  () |> (generateEnvFromBoolT v t >> auxNewCT con t) )
                |> ignore
            | IfWithin (v, date, con1, con2) ->
                let maxDay = addDates date timeExtend
                [timeExtend .. maxDay] |> List.iter (fun t ->  () |> (generateEnvFromBoolT v t >> auxNewCT con1 t) )
                ()  |> (auxNewCT con2 (maxDay+1))
            | VarC n                    -> () |> auxNewC (getLetVariable n letConEnv "contract")
            | LetR(n, eRhs, eBody)      -> () |> (generateEnvFromReal eRhs >> aux eBody timeExtend letBoolEnv (Map.add n (Real 0.0 |> Variable) letRealEnv) letConEnv)
            | LetB(n, eRhs, eBody)      -> () |> (generateEnvFromBool eRhs >> aux eBody timeExtend (Map.add n (Bool false |> Variable) letBoolEnv) letRealEnv letConEnv)
            | LetC(n, eRhs, eBody)      -> () |> (auxNewC eRhs >> (aux eBody timeExtend letBoolEnv letRealEnv (Map.add n (Variable Zero) letConEnv)))
            | LetFunC(n, args, eRhs, eBody)     ->
                let closurec = LetFunCToClosure args eRhs letBoolEnv letRealEnv letConEnv 
                () |> aux eBody timeExtend letBoolEnv letRealEnv (Map.add n closurec letConEnv)
            | LetFunB(n, args, eRhs, eBody)     ->
                let closureb = LetFunBToClosure args eRhs letBoolEnv letRealEnv 
                () |> aux eBody timeExtend (Map.add n closureb letBoolEnv) letRealEnv letConEnv
            | LetFunR(n, args, eRhs, eBody)     ->
                let closurer = LetFunRToClosure args eRhs letRealEnv 
                () |>  aux eBody timeExtend letBoolEnv (Map.add n (closurer) letRealEnv) letConEnv
            | IterCon(n,v,i,di)         ->
                fun (i,di) ->
                    let (eBody, (letBoolEnv, letRealEnv, letConEnv)) = getMapContractAndAddClosure n [v|> VCon] letConEnv
                    [0..(i-1)] |> List.iter (fun t -> ()|> aux eBody (timeExtend + (t*di)) letBoolEnv letRealEnv letConEnv)
                |> matchFoldFailIfNone evalReal i di 
            | CallC (n, args)           ->
                args |> List.iter (fun v -> match v with | VCon c -> () |> auxNewC c | VBool b -> () |> generateEnvFromBool b | VReal r -> () |> generateEnvFromReal r   )
                let (eBody, (letBoolEnv, letRealEnv, letConEnv)) = getMapContractAndAddClosure n args letConEnv
                () |> aux eBody timeExtend letBoolEnv letRealEnv letConEnv
        aux c t Map.empty Map.empty Map.empty |> ignore
        obsEnv

    let evalTest1 () = eval (test7)
    let evalTest2 () = eval (test8)
    let evalTest3 () = eval (test9)
    let evalTest4 () = eval (test10)
    let evalTest5 () = eval (test11)
    let evalTest6 () = eval (test12)
    let evalTest7 () = eval (test13)
    let evalTest8 () = eval (test17)

    let generateRealEnvTest test = generateEnvs test 0 (emptyObsEnv ()) 
     