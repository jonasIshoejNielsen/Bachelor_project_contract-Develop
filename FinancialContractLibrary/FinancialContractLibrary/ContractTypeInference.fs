module ContractTypeInference
    open ContractTypes
    open ContractHelperFunctions
    let ifValueIsTypRThenTypX x v = match v with | Some TypR -> Some x | _ -> None
    let ifValueIsTypBThenTypX x v = match v with | Some TypB -> Some x | _ -> None
    let ifValueIsTypCThenTypX x v = match v with | Some TypC -> Some x | _ -> None
    let unify v1 v2 = 
        match v1, v2 with
        | Some TypC, Some TypC -> Some TypC
        | Some TypR, Some TypR -> Some TypR
        | Some TypB, Some TypB -> Some TypB
        | _                    -> None
    
    let variableInMap n map acc = match Map.tryFind n map with | None -> false | Some v -> match v with | Closure _ -> false | Variable _ -> acc
    let closureInMap n map = match Map.tryFind n map with | None -> None | Some v -> match v with | Closure (arg, body, env) -> Some (arg, body, env) | _ -> None
    
    
    ///<summary>Add parameters to map </summary>
    let AddArgsToMap arg args (m1,m2,m3) = 
        List.zip arg args
        |> Map.ofList
        |> Map.fold (fun (m1,m2,m3) k v ->
            match v with
            | VReal v -> (m1, Map.add k (v |> Variable) m2, m3)
            | VBool v -> (Map.add k (v|> Variable)  m1, m2, m3)
            | VCon v -> (m1, m2, Map.add k (Variable v)  m3)
            ) (m1,m2,m3) 
    
    ///<summary>Test if a Real have correct type </summary>
    let rec typReal v letRealEnv c =
        match v with
        | Real _                -> Some TypR |> c
        | Add(v1, v2)
        | Sub(v1, v2)
        | Max(v1,v2)
        | Mul(v1, v2)-> typReal v1 letRealEnv (fun v1 -> typReal v2 letRealEnv (fun v2-> unify v1 v2 |> ifValueIsTypRThenTypX TypR |> c))
        | Pow(v1,_)             -> typReal v1 letRealEnv (fun v1 -> ifValueIsTypRThenTypX TypR v1 |> c)
        | ObsReal _             -> Some TypR |> c
        | FoldReal(n,v, acc, i, di)    ->
            let (eBody, letRealEnv2) = getMapRealAndAddClosure n [Real 0.0 |> VReal; v |> VReal] letRealEnv
            typReal eBody letRealEnv2 (fun v -> typReal acc letRealEnv (fun vacc -> unify v vacc |> c))
        | VarR _                -> Some TypR |> c
        | CallR(n, args)        ->
            let (eBody, letRealEnv) = getMapRealAndAddClosure n args letRealEnv
            typReal eBody letRealEnv (fun v -> v |> c)
    
    ///<summary>Test if a Bool have correct type </summary>
    let rec typBool v letBoolEnv letRealEnv  c =
        let typBoolNewB b = typBool b letBoolEnv letRealEnv 
        let typReal v1 = typReal v1 letRealEnv
        match v with
        | Bool _                -> Some TypB |> c
        | BAnd(v1, v2)
        | BOr(v1, v2)           -> typBoolNewB v1 (fun v1 -> typBoolNewB v2 (fun v2-> unify v1 v2 |> ifValueIsTypBThenTypX TypB |> c))
        | BNot(v1)              -> typBoolNewB v1 (fun v1 -> ifValueIsTypBThenTypX TypB v1 |> c)
        | RLT(v1, v2)
        | RGT(v1, v2)
        | REQ(v1, v2)
        | RLTEQ(v1, v2)
        | RGTEQ(v1, v2)         -> typReal v1 (fun v1 -> typReal v2 (fun v2-> unify v1 v2 |> ifValueIsTypRThenTypX TypR |> ifValueIsTypRThenTypX TypB |> c))
        | ObsBool _             -> Some TypB |> c
        | BoolIf (v1, v2, v3)    ->
            typBoolNewB v1 (fun v1 -> typBoolNewB v2 (fun v2 -> typBoolNewB v3 (fun v3->
                match v1 with
                | Some TypB -> unify v2 v3 |> c
                |_          -> None |> c    
            )))
        | FoldBool(n, v, acc, i, di)    ->
            let (eBody, (letBoolEnv, letRealEnv)) = getMapBoolAndAddClosure n [Bool true |> VBool; v|> VBool] letBoolEnv
            typBool eBody letBoolEnv letRealEnv (fun v -> typBoolNewB acc (fun vacc-> unify v vacc |> c))
        | VarB _                -> Some TypB |> c
        | CallB(n, args)        ->
            let (eBody, (letBoolEnv, letRealEnv)) = getMapBoolAndAddClosure n args letBoolEnv
            typBool eBody letBoolEnv letRealEnv  (fun v -> v |> c)

    ///<summary>Test if a Contract have correct type </summary>
    let typ con = 
        let rec typ con letBoolEnv letRealEnv letConEnv c =
            let typNewC con = typ con letBoolEnv letRealEnv letConEnv
            let typBool b = typBool b letBoolEnv letRealEnv
            let typReal v = typReal v letRealEnv
            match con with 
            | Zero                      -> Some TypC |> c
            | Pay(_,v,_,_,_)            -> typReal v (fun v -> ifValueIsTypRThenTypX TypC v |> c)
            | And(c1, c2)               -> typNewC c1 (fun v1 -> typNewC c2 (fun v2 -> unify v1 v2 |> ifValueIsTypCThenTypX TypC |> c))
            | Scale (c1,_)
            | Shift (c1,_)              -> typNewC c1 c
            | If(v, c1, c2)             ->
                typBool v
                    (fun v1 -> typNewC c1 (fun v2 -> typNewC c2 (fun v3 ->
                        ifValueIsTypBThenTypX TypC v1 |> unify v2  |> unify v3 |> ifValueIsTypCThenTypX TypC |> c
                    )))
            | IfUnbound(v,c1)     ->
                typBool v
                    (fun v1 -> typNewC c1 (fun v2 ->
                        ifValueIsTypBThenTypX TypC v1 |> unify v2  |> ifValueIsTypCThenTypX TypC |> c
                    ))
            | IfWithin(v,_, c1, c2)     ->
                typBool v
                    (fun v1 -> typNewC c1 (fun v2 -> typNewC c2 (fun v3 ->
                        ifValueIsTypBThenTypX TypC v1 |> unify v2  |> unify v3 |> ifValueIsTypCThenTypX TypC |> c
                    )))
            | VarC _                    -> Some TypC |> c
            | LetR(n,erhs,eBody)        ->
                typReal erhs (fun v1 -> match v1 with | Some TypR -> typ eBody letBoolEnv (Map.add n (Real 0.0 |> Variable) letRealEnv) letConEnv (fun v2 -> v2 |> c) | _         -> None |> c )
            | LetB(n,erhs,eBody)        ->
                typBool erhs (fun v1 -> match v1 with | Some TypB -> typ eBody (Map.add n (Bool true |> Variable) letBoolEnv) letRealEnv letConEnv (fun v2 -> v2 |> c) | _         -> None |> c )
            | LetC(_,eRhs,eBody)        -> typNewC eRhs (fun v1 ->  typNewC eBody (fun v2  ->unify v1 v2 |> ifValueIsTypCThenTypX TypC |> c)) 
            | LetFunC(n, args, eRhs, eBody) ->
                let closurec = LetFunCToClosure args eRhs letBoolEnv letRealEnv letConEnv 
                typ eBody letBoolEnv letRealEnv (Map.add n (closurec) letConEnv) c
            | LetFunB(n, args, eRhs, eBody) ->
                let closureb = LetFunBToClosure args eRhs letBoolEnv letRealEnv 
                typ eBody (Map.add n (closureb) letBoolEnv) letRealEnv letConEnv c
            | LetFunR(n, args, eRhs, eBody) ->
                let closurer = LetFunRToClosure args eRhs letRealEnv 
                typ eBody letBoolEnv (Map.add n (closurer) letRealEnv) letConEnv c
            | IterCon(n,v,i,di)         ->
                let (eBody, (letBoolEnv, letRealEnv, letConEnv)) = getMapContractAndAddClosure n [v|>VCon] letConEnv
                typ eBody letBoolEnv letRealEnv letConEnv c
            | CallC(n, args)            ->
                let (eBody, (letBoolEnv, letRealEnv, letConEnv)) = getMapContractAndAddClosure n args letConEnv
                typ eBody letBoolEnv letRealEnv letConEnv c
        typ con Map.empty Map.empty Map.empty id
        |> function | None -> false | _ -> true

    
    ///<summary>Test if a Real have unbound variables </summary>
    let unBoundTestReal r letRealEnv acc c=
        let rec aux r letRealEnv acc c =
            if not acc then false |> c
            else 
                match r with 
                | ObsReal _
                | Real _                 -> acc|> c
                | Add(r1, r2)
                | Sub(r1,r2)
                | Mul(r1,r2)
                | Max(r1,r2)             -> aux r1 letRealEnv acc (fun acc -> aux r2 letRealEnv acc c)
                | FoldReal(n, v, ac, i, di)     ->
                    match i, di with
                    | Real _, Real _ ->
                        match closureInMap n letRealEnv with
                        | None -> false
                        | Some (arg, eBody, env) -> 
                            match (List.length arg = 2), env with
                            | true, MapReal(renv)->
                                let (_, letRealEnv, _) = AddArgsToMap arg [Real 0.0 |> VReal; v|> VReal] (Map.empty, renv, Map.empty)
                                aux ac letRealEnv acc (fun acc -> aux eBody letRealEnv acc c)
                            | _, _ -> false |> c
                    | _, _ -> false
                | Pow(r1,_)              -> aux r1 letRealEnv acc c
                | VarR n                 -> acc |> variableInMap n letRealEnv |> c
                | CallR(n, args)         ->                                
                    match closureInMap n letRealEnv with
                    | None -> false
                    | Some (arg, eBody, env) -> 
                        match (List.length arg = List.length args), env with
                        | true, MapReal(renv)->
                            let (_, letRealEnv, _) = AddArgsToMap arg args (Map.empty, renv, Map.empty)
                            let acc = List.fold (fun acc v ->  match v with | VReal r -> aux r letRealEnv acc id | _ -> false) acc args
                            aux eBody letRealEnv acc c
                        | _, _ -> false|> c
        aux r letRealEnv acc c
    
    ///<summary>Test if a Bool have unbound variables </summary>
    let unBoundTestBool b letBoolEnv letRealEnv acc c=
        let rec aux b letBoolEnv letRealEnv acc c =
            let auxNewB b = aux b letBoolEnv letRealEnv
            let TestReal r = unBoundTestReal r letRealEnv
            if not acc then false |> c
            else 
                match b with 
                | ObsBool _
                | Bool _                 -> acc |> c
                | BAnd(b1,b2)
                | BOr(b1,b2)             -> auxNewB b1 acc (fun acc -> auxNewB b2 acc c)
                | BoolIf(b1,b2, b3)      -> auxNewB b1 acc (fun acc -> auxNewB b2 acc (fun acc -> auxNewB b3 acc c))
                | RLT(r1,r2)
                | RGT(r1,r2)
                | REQ(r1,r2)
                | RLTEQ(r1,r2)
                | RGTEQ(r1,r2)           -> TestReal r1 acc (fun acc -> TestReal r2 acc c) 
                | BNot (b1)              -> auxNewB b1 acc c
                | FoldBool(n, v, ac, i, di)     ->
                    match i, di with
                    | Real _, Real _ ->
                        match closureInMap n letBoolEnv with
                        | None -> false |> c
                        | Some (arg, eBody, env) -> 
                            match (List.length arg = 1), env with
                            | true, MapBool(benv, renv)->
                                let (letBoolEnv, letRealEnv, _) = AddArgsToMap arg [Bool true |> VBool; v|> VBool] (benv, renv, Map.empty)
                                auxNewB ac acc (fun acc -> aux eBody letBoolEnv letRealEnv acc c)
                            | _, _ -> false|> c
                    | _, _ -> false
                | VarB n                 -> acc |> variableInMap n letBoolEnv
                | CallB(n, args)         ->                                
                    match closureInMap n letBoolEnv with
                    | None -> false
                    | Some (arg, eBody, env) -> 
                        match (List.length arg = List.length args), env with
                        | true, MapBool(benv, renv)->
                            let (letBoolEnv, letRealEnv, _) = AddArgsToMap arg args (benv, renv, Map.empty)
                            let acc = List.fold (fun acc v ->  match v with | VReal r -> TestReal r acc id | VBool b -> auxNewB b acc id | VCon c -> false) acc args
                            aux eBody letBoolEnv letRealEnv acc c
                        | _, _ -> false
        aux b letBoolEnv letRealEnv acc c
    
    ///<summary>Test if a Contract have unbound variables </summary>
    let unBoundTestCon con =
        let rec aux con (letBoolEnv:Map<string, LetType<Bool>>) (letRealEnv:Map<string, LetType<Real>>) letConEnv acc c=
            let auxNewC c = aux c letBoolEnv letRealEnv letConEnv
            let TestReal r = unBoundTestReal r letRealEnv
            let TestBool b = unBoundTestBool b letBoolEnv letRealEnv
            if not acc then false |> c
            else 
                match con with
                | Zero                  -> acc |> c
                | Pay(_,r,_,_,_)        -> TestReal r acc c
                | And (c1,c2)           -> auxNewC c1 acc (fun acc -> auxNewC c2 acc c)
                | Scale(c1, _)
                | Shift(c1, _)          -> auxNewC c1 acc c
                | If(b, c1, c2)
                | IfWithin(b, _, c1, c2)-> TestBool b acc (fun acc -> auxNewC c1 acc (fun acc -> auxNewC c2 acc c))
                | IfUnbound(b, c1)      -> TestBool b acc (fun acc ->  auxNewC c1 acc c)
                | VarC n                -> acc |> variableInMap n letConEnv |> c
                | LetR(n, eRhs, eBody)  -> TestReal eRhs acc (fun acc -> aux eBody letBoolEnv (Map.add n (0.0 |> Real |> Variable) letRealEnv) letConEnv acc c)
                | LetB(n, eRhs, eBody)  -> TestBool eRhs acc (fun acc -> aux eBody (Map.add n (true |> Bool |> Variable) letBoolEnv) letRealEnv letConEnv acc c)
                | LetC(n, eRhs, eBody)  -> auxNewC eRhs acc (fun acc -> aux eBody letBoolEnv letRealEnv (Map.add n (Variable Zero) letConEnv) acc c)
                | LetFunC(n, args, eRhs, eBody) -> 
                    let closure = LetFunCToClosure args eRhs letBoolEnv letRealEnv letConEnv
                    aux eBody letBoolEnv letRealEnv (Map.add n closure letConEnv) acc c
                | LetFunB(n, args, eRhs, eBody) -> 
                    let closure = LetFunBToClosure args eRhs letBoolEnv letRealEnv
                    aux eBody (Map.add n closure letBoolEnv) letRealEnv letConEnv acc c
                | LetFunR(n, args, eRhs, eBody) -> 
                    let closure = LetFunRToClosure args eRhs letRealEnv
                    aux eBody letBoolEnv (Map.add n closure letRealEnv) letConEnv acc c
                | IterCon(n,v,i,di)             ->
                    match closureInMap n letConEnv with
                    | None -> false
                    | Some (arg, eBody, env) -> 
                        match (List.length arg = 1), env with
                        | true, MapContract(benv, renv, cenv)->
                            let (letBoolEnv, letRealEnv, letConEnv) = AddArgsToMap arg [v|>VCon] (benv, renv, cenv)
                            let acc = List.fold (fun acc v ->  match v with | VReal r -> TestReal r acc id | VBool b -> TestBool b acc id | VCon c -> auxNewC c acc id) acc [v|>VCon]
                            aux eBody letBoolEnv letRealEnv letConEnv acc c
                        | _, _ -> false
                | CallC (n, args)       ->
                    match closureInMap n letConEnv with
                    | None -> false
                    | Some (arg, eBody, env) -> 
                        match (List.length arg = List.length args), env with
                        | true, MapContract(benv, renv, cenv)->
                            let (letBoolEnv, letRealEnv, letConEnv) = AddArgsToMap arg args (benv, renv, cenv)
                            let acc = List.fold (fun acc v ->  match v with | VReal r -> TestReal r acc id | VBool b -> TestBool b acc id | VCon c -> auxNewC c acc id) acc args
                            aux eBody letBoolEnv letRealEnv letConEnv acc c
                        | _, _ -> false

        aux con Map.empty Map.empty Map.empty true id









