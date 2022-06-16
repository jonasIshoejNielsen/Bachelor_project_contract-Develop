module ContractHelperFunctions
    open ContractTypes
    
    let addDates d time = d+time
    let tolerance = 0.0001        //todo make a better tolerance
    let (=~) x1 x2 = abs(x1 - x2) < tolerance
    let (<=~) x1 x2 = x1 < x2 || x1 =~ x2
    let (>=~) x1 x2 = x1 > x2 || x1 =~ x2
    let (^~) x1 f = if x1 <=~0.0 then - (abs(x1)**f) else x1 ** f
    let LetFunCToClosure args eRhs letBoolEnv letRealEnv letConEnv = Closure (args, eRhs, MapContract(letBoolEnv, letRealEnv, letConEnv))
    let LetFunBToClosure args eRhs letBoolEnv letRealEnv           = Closure (args, eRhs, MapBool(letBoolEnv, letRealEnv))
    let LetFunRToClosure args eRhs letRealEnv                      = Closure (args, eRhs, MapReal(letRealEnv))
    
    ///<summary>Add to environments the keys from arg mapped to values from args</summary>
    let AddClosureToConEnv arg args (letBoolEnv, letRealEnv, letConEnv)= 
        List.zip arg args
        |> List.fold (fun (letBoolEnv, letRealEnv, letConEnv) (n, eRhs) -> 
            match eRhs with
            | VReal r -> (letBoolEnv, Map.add n (r|> Variable) letRealEnv, letConEnv)
            | VBool b -> (Map.add n (b|> Variable) letBoolEnv, letRealEnv, letConEnv)
            | VCon c  -> (letBoolEnv, letRealEnv, Map.add n (c|> Variable) letConEnv)
        ) (letBoolEnv, letRealEnv, letConEnv)
    
    ///<summary>Get variable n from env, if not there raise exception with typeString msg</summary>
    let getLetVariable n letRealEnv typeString = 
        match Map.tryFind n letRealEnv with
        | Some v -> 
            match v with
            | Variable v -> v 
            | _ -> ReferencedFunctionExpectedVar n |> raise 
        | None ->
            UnBoundException (n, typeString) |> raise 
        
    ///<summary>Get closure n from env, if not there raise exception with typeString msg</summary>
    let getLetClosure n letRealEnv typeString = 
        match Map.tryFind n letRealEnv with
        | Some v -> 
            match v with
            | Closure (arg, body, envs) -> (arg, body, envs) 
            | _ -> ReferencedVarExpectedFunction n |> raise 
        | None -> UnBoundException (n, typeString) |> raise 

    ///<summary>Get env with added value for parameters</summary>
    let getMapContractAndAddClosure n args letConEnv = 
        let (arg, ebody, envs) = getLetClosure n letConEnv "contract"
        match envs with
        | MapContract (letBoolEnv, letRealEnv, letConEnv) -> (ebody, AddClosureToConEnv arg args (letBoolEnv, letRealEnv, letConEnv))
        | _ -> failwith ("wrong map given to function " + n)
    ///<summary>Get env with added value for parameters</summary>
    let getMapBoolAndAddClosure n args letBoolEnv = 
       let (arg, ebody, envs) = getLetClosure n letBoolEnv "bool"
       match envs with
       | MapBool (letBoolEnv, letRealEnv) -> 
            match AddClosureToConEnv arg args (letBoolEnv, letRealEnv, Map.empty) with
            | (letBoolEnv, letRealEnv, letConEnv) when Map.isEmpty letConEnv
                    -> (ebody, (letBoolEnv, letRealEnv))
            | _     -> failwith ("contained an invalid variable")
       | _ -> failwith ("wrong map given to function " + n)
    
    ///<summary>Get env with added value for parameters</summary>
    let getMapRealAndAddClosure n args letRealEnv = 
        let (arg, ebody, envs) = getLetClosure n letRealEnv "real"
        match envs with
        | MapReal (letRealEnv) -> 
            let k = AddClosureToConEnv arg args (Map.empty, letRealEnv, Map.empty)
            match AddClosureToConEnv arg args (Map.empty, letRealEnv, Map.empty) with
            | (letBoolEnv, letRealEnv, letConEnv) when Map.isEmpty letConEnv && Map.isEmpty letBoolEnv
                    -> (ebody, letRealEnv)
            | _     -> failwith ("contained an invalid variable")
        | _ -> failwith ("wrong map given to function " + n)

    let emptyObsEnv () = { count = None; boolObsEnv = Map.empty; realObsEnv = Map.empty}
    let unboundHorizonDays = 1000
    let listFromNotToMax timeExtend = [timeExtend .. (addDates unboundHorizonDays timeExtend)]
    let mapArg fb fr fc =
        let ifNone v acc f=
            match acc, v with
            | None,_ 
            | _, None -> None
            | Some acc, Some v -> Some ((f v) :: acc)
        List.rev
        >> List.fold (fun acc v ->
            match v with
            | VBool b   -> ifNone (fb b) acc (Bool >> VBool)
            | VReal r   -> ifNone (fr r) acc (Real >> VReal) 
            | VCon c    -> ifNone (fc c) acc (VCon)
            ) (Some [])
    let mapType fb fr fc = List.map(fun v -> match v with | TypB -> fb () |> VBool | TypR -> fr() |> VReal | TypC -> fc () |> VCon)

    
    let (>>=) x switch1  =
        match x with
        | true -> switch1 true
        | false -> false