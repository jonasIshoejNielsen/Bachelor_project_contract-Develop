module ContractRandomGenerator
    open System
    open ContractHelperFunctions
    open ContractTypes

    type EnvGen = 
        | GenVal of string
        | GenClosure of string * TypeInferenceType list
    ///<summary>Set containing created let names and funciton call name*type</summary>
    type MutableSet = {mutable set:  Set<EnvGen>}
    
    ///<summary>Pick random weighted options for list (weight, value)</summary>
    let weightedChoise lst (random:Random) () = 
        let choise = random.Next(0, lst |> List.fold (+) 0) 
        lst 
        |> List.indexed
        |> List.fold (fun acc (i,v) ->
            match acc with
            | (Some _, _) -> acc
            | (_, va) -> if va + v <choise then (None,va + v) else (Some i, 0)
            ) (None, 0)
        |> fst 
        |> Option.get
    
    ///<summary>If test >= maxTests get a random int between 0 and choise//not including choise, else call f </summary>
    let cutOffOrWiehgtedChoise test maxTests choise f (random:Random) = 
        if test >= maxTests then random.Next(0,choise) else f ()
    
    let randomElementSet       lst= lst |> Set.toList|> List.item ((new Random ()).Next (lst|>Set.count))
    let randomElementList      lst= lst |> List.item ((new Random ()).Next (lst|>List.length))

    let randomString        n  = 
        let r = Random()
        let chars = Array.concat([[|'a' .. 'z'|];[|'A' .. 'Z'|];[|'0' .. '9'|]])
        let sz = Array.length chars
        (fun _ -> chars.[r.Next sz])
        |> Array.init n |> String
    let randomBoolValue     () = (new Random ()).Next(2) |> (=) 0 |> Bool
    let randomFloat         () = (float((new Random ()).Next (0, 100))) / 10.0
    let randomInt           max = (new Random ()).Next (0, max)
    let randomDate          () = randomInt 1000
    let randomParty         () = randomString 1     //todo replce with combo below, maybe
        //let combos = ["x"; "You"; "me"; "y"; "bob"; "dod"; "bod"; "dob"]
        //List.item ((new Random ()).Next(combos.Length)) combos
    let randomCurrency      () = [DKK; EURO; USD]   |> randomElementList
    let randomType          () = [TypR; TypB; TypC] |> randomElementList
    let rec randomlabel     () = 
        let f = 
            [randomParty>>Defaults; randomParty >> Exercises; randomCurrency>>Business; (fun () -> (randomlabel (), randomInt 100)) >>Pickable; (fun () -> randomString 5) >>Action ]
            |> randomElementList
        f ()
    let randomObs         obsT = obsT (randomDate (), randomlabel ())
    let randomTypeInferenceTypeList count = List.init count (fun _ -> randomType ())

    let randomVar varT env = (randomString 5) |> fun n ->  env.set <- env.set |> Set.add(GenVal n ); varT n

    let randomCall callT env fb fr fc filterSet= 
        let n, lst = (randomString 5), randomTypeInferenceTypeList 6|> List.filter(fun v -> Set.contains v filterSet )
        env.set <- env.set |> Set.add(GenClosure (n,lst) )
        callT (n, lst |> mapType fb fr fc)
    
    ///<summary>Generate random Real</summary>
    let randomReal realEnv random _ =
        let maxTests = 3
        let weightedChoise = weightedChoise [8; 8; 2; 2; 6; 6; 6; 6; 6 ] random
        let cutOffOrWiehgtedChoise test = cutOffOrWiehgtedChoise test maxTests 2 weightedChoise random
        
        let filterSet = Set.empty |> Set.add TypR
        let rec create c test = 
            let create c = create c (test + 1)
            let combine2 f  = create (fun r1 -> create (fun r2 -> f(r1,r2) |> c))

            match cutOffOrWiehgtedChoise test with
            | 0  -> randomFloat () |> Real |> c
            | 1  -> randomObs ObsReal |> c
            | 2 -> randomCall CallR realEnv (fun _ -> Bool true) (fun _ -> create id) (fun _ -> Zero) filterSet |> c
            | 3 -> randomVar VarR realEnv |> c
            | 4  -> combine2 Add
            | 5  -> combine2 Sub
            | 6  -> combine2 Mul
            | 7  -> combine2 Max
            | _  -> create (fun r1 -> Pow(r1, randomFloat () / 4.0) |> c)
        create id 0
        //randomFloat ()  |> Real
    
    ///<summary>Generate random Bool</summary>
    let randomBool boolEnv realEnv random _ = 
        let maxTests = 3
        let weightedChoise = weightedChoise [8; 8; 1; 1; 6; 6; 6; 6; 6; 6; 6; 6; 6 ] random
        let cutOffOrWiehgtedChoise test = cutOffOrWiehgtedChoise test maxTests 9 weightedChoise random
        let randomReal = randomReal realEnv random
        let filterSet = [TypR; TypB] |> Set.ofList

        let rec create c test = 
            let create c = create c (test + 1)
            match cutOffOrWiehgtedChoise test with
            | 0  -> randomBoolValue () |> c
            | 1  -> randomObs ObsBool  |> c
            | 2 -> randomCall CallB boolEnv (fun _ -> create id) randomReal (fun _ -> Zero) filterSet|> c
            | 3  -> randomVar VarB boolEnv |> c
            | 4  -> RLT(randomReal (), randomReal ()) |> c
            | 5  -> RGT(randomReal (), randomReal ()) |> c
            | 6  -> REQ(randomReal (), randomReal ()) |> c
            | 7  -> RLTEQ(randomReal (), randomReal ()) |> c
            | 8  -> RGTEQ(randomReal (), randomReal ()) |> c
            | 9  -> create (fun v1 -> create (fun v2 -> BOr(v1, v2) |> c))
            | 10 -> create (fun v1 -> BNot(v1) |> c)
            | 11 -> create (fun v1 -> create (fun v2 -> BAnd(v1, v2) |> c))
            | _  -> create (fun v1 -> create (fun v2 -> create (fun v3 -> BoolIf(v1, v2, v3) |> c)))
        create id 0
    
    ///<summary>Add generated variable or call to set of calls </summary>
    let addSetToC env maxTests fc letT letFunT acc =
        env.set
        |> Set.fold (fun acc v -> 
            match v with
            | GenVal n -> letT (n, (fc (maxTests-3)), acc)
            | GenClosure (n, lst) -> letFunT (n, lst|>List.map(fun _ -> randomString 5) , (fc (maxTests-3)), acc)
        ) acc
    ///<summary>Generate random contract</summary>
    let rec randomContract size :Contract =
        let random = new Random ()
        let maxTests = 3
        let weightedChoise = weightedChoise [8; 8; 1; 1; 8; 6; 6; 6; 6; 6; 6 ] random
        let cutOffOrWiehgtedChoise test = cutOffOrWiehgtedChoise test maxTests 2 weightedChoise random
        let filterSet = [TypC; TypB; TypR] |> Set.ofList
    
        let boolEnv, realEnv, conEnv = { set = Set.empty}, { set = Set.empty}, { set = Set.empty}
        let rec randomContract size boolEnv realEnv conEnv =

            let randomBool2 = randomBool boolEnv realEnv random 
            let randomReal2 = randomReal realEnv random
        
            let rec addVarAndFunc boolEnv realEnv conEnv con=
                let boolEnv2, realEnv2, conEnv2 = { set = Set.empty}, { set = Set.empty}, { set = Set.empty}
                con
                |> addSetToC conEnv maxTests (fun _ -> randomContract size boolEnv2 realEnv2 conEnv2)  LetC LetFunC
                |> addSetToC boolEnv maxTests (fun _ -> randomBool boolEnv2 realEnv2 random ()) LetB LetFunB
                |> addSetToC realEnv maxTests (fun _ -> randomReal realEnv2 random ()) LetR LetFunR
                |> fun con ->
                    if boolEnv2.set |> Set.isEmpty &&  realEnv2.set |> Set.isEmpty && conEnv2.set |> Set.isEmpty 
                    then con else addVarAndFunc boolEnv2 realEnv2 conEnv2 con
        
            let rec aux test c : Contract= 
                let create c = aux (test + 1) c
                match cutOffOrWiehgtedChoise test with
                | 0 -> Zero |> c
                | 1 -> (randomCurrency (), randomReal2 (), randomDate (), randomParty (), randomParty ()) |> Pay  |> c
                | 2 -> randomCall CallC conEnv randomBool2 randomReal2 (fun _ -> create id) filterSet|> c
                | 3 -> randomVar VarC conEnv |> c
                | 4 -> create (fun v1 -> create (fun v2 -> And (v1,v2) |> c))
                | 5 -> create (fun v1 -> (v1, randomReal2 ()) |> Scale |> c)
                | 6 -> create (fun v1 -> (v1, randomDate ()) |> Shift |> c)
                | 7 -> create (fun v1 -> create (fun v2 -> If (randomBool2 (), v1,v2) |> c))
                | 8 -> create (fun v1 -> create (fun v2 -> IfWithin (randomBool2 (), randomDate (), v1,v2) |> c))
                | 9 -> create (fun v1 -> IfUnbound (randomBool2 (), v1))
                | _ -> 
                    let n = randomString 5
                    conEnv.set <- conEnv.set |> Set.add(GenClosure (n,[TypC]) )
                    create (fun v -> IterCon(n, v, 10 |> randomInt |> float |>Real, 100 |> randomInt |> float |>Real ))
            (aux size id) 
            |> addVarAndFunc boolEnv realEnv conEnv
        randomContract size boolEnv realEnv conEnv
        
