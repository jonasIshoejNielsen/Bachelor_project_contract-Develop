module MaxValueContractsProperty
    open ContractTypes
    open ContractHelperFunctions
    open ContractEval
    open System
    open TransactionProperties
    open ContractSimplify

    ///<summary>Increment value if in map, else add to map, for functions</summary>
    let addIncrementValueToMap key v m =
        match Map.tryFind key m with
        | Some vold -> Map.add key (v+vold) m 
        | None      -> Map.add key v m
     
    type closureRMaxValue = | CRMax of string list* Real * Map<string, (float*float)> * Map<string,closureRMaxValue>

    type closureCMaxValue = | CCMax of string list* Contract * Map<string, (float*float)> * Map<string,closureRMaxValue> * Map<string, float> * Map<string, closureCMaxValue> 
 
    let testBoolIfAlwaysTrue b =
        match simplifyB b with
        | Bool b -> Some b
        | _ -> None
    
    ///<summary>Get maxvalue for a real, assuming observables have range [-1000, 1000]</summary>
    let maxValueReal r letRealEnv letFunRealEnv=
        let valueObs = -1000., 1000.

        let rec aux r letRealEnv letFunRealEnv c =
            let auxNewr r = aux r letRealEnv letFunRealEnv
            let compare2 r1 r2 op = auxNewr r1 (fun (v11, v12) -> auxNewr r2 (fun (v21, v22) -> (op v11 v21, op v12 v22) |> c  ))
            let compare1 r1 op    = auxNewr r1 (fun (v1, v2) -> (op v1, op v2) |> c  )
            match r with
            | Real r                    -> (r,r) |> c
            | Add (v1, v2)              -> compare2 v1 v2 (+)
            | Sub (v1, v2)              -> compare2 v1 v2 (-)
            | Max(v1,v2)                -> compare2 v1 v2 (max)
            | Mul (v1, v2)              -> compare2 v1 v2 (*)
            | Pow (v1, f)               -> compare1 v1 (fun v1 -> v1^~f)
            | ObsReal (_, _)            -> valueObs|> c
            | FoldReal (n,v,ac, i, di)  ->
                let arg, eRhs, letRealEnv, letFunRealEnv= match Map.find n letFunRealEnv with | CRMax (arg, eRhs, letRealEnv, letFunRealEnv) -> arg, eRhs, letRealEnv, letFunRealEnv
                let letRealEnv = letRealEnv |> Map.add arg.Tail.Head (auxNewr v id)
                let foldFun acc _ =
                    let letRealEnv = letRealEnv |> Map.add arg.Head acc
                    aux eRhs letRealEnv letFunRealEnv id
                let acc = auxNewr ac id
                [0..(auxNewr i id |> snd|>int)] |> List.fold foldFun (acc)
            | VarR n                    -> Map.find n letRealEnv
            | CallR (n,args)            ->
                let arg, eRhs, letRealEnv, letFunRealEnv= match Map.find n letFunRealEnv with | CRMax (arg, eRhs, letRealEnv, letFunRealEnv) -> arg, eRhs, letRealEnv, letFunRealEnv
                let addEnvs acc n v = 
                    match v with
                    | VReal r -> Map.add n (auxNewr r id) acc
                    | _  -> acc
                let letRealEnv = args |> List.fold2 (addEnvs) letRealEnv arg
                aux eRhs letRealEnv letFunRealEnv c
             
        aux r letRealEnv letFunRealEnv id

    ///<summary>Get maxvalue for a contract for party p</summary>
    let maxValueContract c currencyExchangeValue p =

        let rec aux con scale letRealEnv letFunRealEnv letConEnv (letFunConEnv: Map<string, closureCMaxValue>) c :float=
            let auxNewc con c = aux con scale letRealEnv letFunRealEnv letConEnv letFunConEnv c
            let auxNewScale con scale c=
                aux con scale letRealEnv letFunRealEnv letConEnv letFunConEnv c
            let aux2Contracts c1 c2 op = auxNewc c1 (fun v1 -> auxNewc c2 (fun v2 -> (op v1 v2) |> c))
            let maxValueReal r = maxValueReal r letRealEnv letFunRealEnv
            match con with
            | Zero                              -> c 0.0
            | Pay (cur, value, _, p1, p2)       ->
                if p = p1 || p = p2
                then 
                    let convertCurr = currencyExchange currencyExchangeValue cur
                    let value1, value2 = maxValueReal value |> (fun (v1,v2) -> convertCurr v1, convertCurr v2) 
                    let minValue, maxValue = scale * (min value1 value2), scale * (max value1 value2)
                    if p1 = p then -minValue else 0.0
                    |> if p2 = p then (+) maxValue else (+) 0.0
                    |> c
                else c 0.0
            | And (con1, con2)                  -> aux2Contracts con1 con2 (+)
            | Scale (con, i)                    ->
                let scale2 = maxValueReal i |> (fun (v1,v2) -> max (scale * v1) (scale * v2))
                auxNewScale con scale2 c
            | Shift (con, d)                    -> auxNewc con c
            | If (b, con1, con2)                -> 
                match testBoolIfAlwaysTrue b with
                | None   -> aux2Contracts con1 con2 max
                | Some b -> auxNewc (if b then con1 else con2) c
            | IfUnbound (b, con1)               ->
                match testBoolIfAlwaysTrue b with
                | None   -> auxNewc con1 c
                | Some b -> auxNewc (if b then con1 else Zero) c
            | IfWithin (b, date, con1, con2)  -> 
                match testBoolIfAlwaysTrue b with
                | None   -> aux2Contracts con1 con2 max
                | Some b -> auxNewc (if b then con1 else con2) c
            | VarC n                            -> letConEnv |> Map.find n |> c
            | LetR (n, eRhs, eBody)             -> aux eBody scale (Map.add n (maxValueReal eRhs) letRealEnv) letFunRealEnv letConEnv letFunConEnv c
            | LetB (n, eRhs, eBody)             -> auxNewc eBody c
            | LetC (n, eRhs, eBody)             -> aux eBody scale letRealEnv letFunRealEnv (Map.add n (auxNewc eRhs id) letConEnv) letFunConEnv c
            | LetFunC(n, args, eRhs, eBody)     ->
                let closurec  = args, eRhs, letRealEnv, letFunRealEnv, letConEnv, letFunConEnv
                aux eBody scale letRealEnv letFunRealEnv letConEnv (Map.add n (closurec |> CCMax) letFunConEnv) c
            | LetFunB(n, args, eRhs, eBody)     -> auxNewc eBody c
            | LetFunR(n, args, eRhs, eBody)     -> 
                let closurer  = args, eRhs, letRealEnv, letFunRealEnv
                aux eBody scale letRealEnv (Map.add n (CRMax closurer) letFunRealEnv) letConEnv letFunConEnv c
            | IterCon(n,v,i,di)                 ->
                let arg, eRhs, letRealEnv, letFunRealEnv, letConEnv, letFunConEnv =
                    match Map.find n letFunConEnv with | CCMax (arg, eRhs, letRealEnv, letFunRealEnv, letConEnv, letFunConEnv) -> arg, eRhs, letRealEnv, letFunRealEnv, letConEnv, letFunConEnv
                let addEnvs acc n v = 
                    match v with
                    | VBool b -> acc
                    | VReal r -> ((Map.add n (maxValueReal r) (fst acc)) , snd acc)
                    | VCon c  -> (fst acc), Map.add n (auxNewc c id) (snd acc)
                
                let letRealEnv, letConEnv = [v|>VCon] |> List.fold2 (addEnvs) (letRealEnv, letConEnv) arg

                aux eRhs scale letRealEnv letFunRealEnv letConEnv letFunConEnv (fun v -> v * ((maxValueReal i |> snd) + 1.0) |> c)
            | CallC (n,args)                    ->
                let arg, eRhs, letRealEnv, letFunRealEnv, letConEnv, letFunConEnv =
                    match Map.tryFind n letFunConEnv with 
                    | Some (CCMax (arg, eRhs, letRealEnv, letFunRealEnv, letConEnv, letFunConEnv)) -> 
                        arg, eRhs, letRealEnv, letFunRealEnv, letConEnv, letFunConEnv
                    | None -> failwith "Recursion not allowed in maxValueContract"
                let addEnvs acc n v = 
                    match v with
                    | VBool b -> acc
                    | VReal r -> ((Map.add n (maxValueReal r) (fst acc)) , snd acc)
                    | VCon c  -> (fst acc), Map.add n (auxNewc c id) (snd acc)
                let letRealEnv, letConEnv = 
                    args
                    |> List.fold2 (addEnvs) (letRealEnv, letConEnv) arg

                aux eRhs scale letRealEnv letFunRealEnv letConEnv letFunConEnv c
             
        aux c 1.0 Map.empty Map.empty Map.empty  Map.empty id
    
    let foldMaxValue c1 c2 currencyExchangeValue acc parties=
        let foldMaxValue acc p=
            if not acc then false
            else
                maxValueContract c1 currencyExchangeValue p =~ maxValueContract c2 currencyExchangeValue p
                |> (&&) acc
        parties |> Set.fold foldMaxValue acc