module Generators
    open FsCheck
    open FsCheck.Xunit
    open ContractTypes
    open ContractRandomGenerator
    open ContractEval
    open ContractProperties
    open TransactionProperties
    open ContractTypeInference
    open ContractHelperFunctions
    
    type obsEnvForTest = {mutable first:  bool;  mutable obsEnv: ObsEnv}
    
    let shrinkObsEnv obs=
        match obs.first, obs.obsEnv.count with
        | true, _ -> Seq.replicate 1 obs
        | _, Some count ->
            let mapRemoveindex (i:int) =  
                Map.toList >> List.mapi (fun ind t -> (ind <> i, t )) >> List.filter fst >> List.map snd >> Map.ofList
                
            let lenghtR,lenghtB = (Map.count obs.obsEnv.realObsEnv),(Map.count obs.obsEnv.boolObsEnv)
            fun i ->
                if i<lenghtR
                then { first = false; obsEnv = {count = Some (count+1); boolObsEnv = obs.obsEnv.boolObsEnv; realObsEnv = mapRemoveindex i obs.obsEnv.realObsEnv}}
                else { first = false; obsEnv = {count = Some (count+1); boolObsEnv = mapRemoveindex (i-lenghtR) obs.obsEnv.boolObsEnv; realObsEnv = obs.obsEnv.realObsEnv}}
            |> Seq.init (lenghtB+lenghtR)
        | _, _ -> failwith "shouldn't happen"

    let shrinkContract con=
        let rec aux con c = 
            match con with
            | Zero | VarC _ | CallC _ | IterCon _
            | Pay _                                     -> []
            | If (_, con1, con2) 
            | IfWithin (_, _, con1, con2)
            | And (con1, con2)                          -> [con1|>c; con2|>c]
            | Scale (con1, _) | Shift (con1, _)
            | IfUnbound (_, con1)                       -> [con1|>c]
            | LetR (n, eRhs, eBody)                     -> aux eBody (fun eBody -> LetR (n, eRhs, eBody) |> c)
            | LetB (n, eRhs, eBody)                     -> aux eBody (fun eBody -> LetB (n, eRhs, eBody) |> c)
            | LetC (n, eRhs, eBody)                     -> aux eBody (fun eBody -> LetC (n, eRhs, eBody) |> c)
            | LetFunR(n, args, eRhs, eBody)             -> aux eBody (fun eBody -> LetFunR (n, args, eRhs, eBody) |> c)
            | LetFunB(n, args, eRhs, eBody)             -> aux eBody (fun eBody -> LetFunB (n, args, eRhs, eBody) |> c)
            | LetFunC(n, args, eRhs, eBody)             -> aux eBody (fun eBody -> LetFunC (n, args, eRhs, eBody) |> c)
        aux con id 
        |> Seq.ofList

    let shrinkCurrency cur  = 
        let currLst = cur |> Map.toList |> List.indexed
        let listRemoveindex (i:int) acc =  
            currLst
            |> List.fold 
                (fun (b, acc) (ind,(c,v)) -> 
                    if ind <> i then (b,(c,v)::acc)
                    else if v =~ 0.0 then (true, []) else (b, (c,0.0)::acc )) 
                (false,[])
            |> function 
                | true,_ -> acc 
                | _, lst -> acc |> Seq.append (Seq.singleton (lst |> Map.ofList))

        Seq.init (Map.count cur) id
        |> Seq.fold(fun acc i -> listRemoveindex i acc) Seq.empty


    type Generators =
        ///<summary>Arbitrary for obsEnvForTest</summary>
        static member ArbObsEnvForTests () =
            {new Arbitrary<obsEnvForTest>() with
                override x.Generator = gen {return {first=true; obsEnv = emptyObsEnv ()}}
                override x.Shrinker t = shrinkObsEnv t }
        
        ///<summary>Arbitrary for Contract</summary>
        static member ArbContract () =
            {new Arbitrary<Contract>() with
                override x.Generator = gen {return randomContract 0}
                override x.Shrinker t = shrinkContract t }
        
        ///<summary>Arbitrary for Map<Currency, float></summary>
        static member ArbCurrency () =
            {new Arbitrary<Map<Currency, float>>() with
                override x.Generator = gen {
                    let addCurr map cur =  Map.add cur (randomFloat()) map
                    return [DKK; USD; EURO] |> List.fold addCurr Map.empty }
                override x.Shrinker t = shrinkCurrency t }
    
    
    ///<summary>Add obs to test function f</summary>
    let ObsEnvGenerator f = 
        Arb.register<Generators>() |> ignore
        fun (xs:obsEnvForTest) ->
            let (count, xsR, xsB) = xs.obsEnv.count, xs.obsEnv.realObsEnv, xs.obsEnv.boolObsEnv
            let res = f xs.obsEnv
            if xs.first
            then
                xs.obsEnv.count <- Some 0
            else
                xs.obsEnv <- {count=count; realObsEnv=xsR; boolObsEnv=xsB}
            xs.first <- false
            res


    
    ///<summary>Add non-mutable variable to function f</summary>
    let ArbitraryGenerator f = 
        Arb.register<Generators>() |> ignore
        f
