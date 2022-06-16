// Learn more about F# at http://fsharp.org

open System
open ContractTypes
open ContractRandomGenerator
open ContractPrint
open ContractEval
open ContractProperties
open TransactionProperties
open ContractTypeInference
open ContractSimplify
open ContractHelperFunctions

let printTest test title number =
    printfn title
    let obsEnv = generateRealEnvTest test
    printfn "Your env : %A" obsEnv
    printfn "Your evaluated contract %s : " number
    (eval test obsEnv |> TransactionsPrint)
    printfn "Expect true because bound : %A" (unBoundTestCon test)
    printfn "typ expect true : %A" (typ test)
    printfn "Observables : %A" (setOfObservables test)
    //printfn "Observables lenght : %A" (setOfObservables test |> fun (v1, v2) -> List.length v1, List.length v2)
    printfn "Parties : %A" (setOfParties test)
    printfn "Test : %A" test
    printfn "Simplified : %A" (simplifyC test)
    printfn ""
    printfn ""

let identical currencyExchangeValue c1 c2 = 
    let obs = emptyObsEnv ()
    let allProperties (t1, t2) = 
        match t1,t2 with
        | Some t1',Some t2' ->
            let parties1 = setOfPartiesFromTrans t1' true
            let parties2 = setOfPartiesFromTrans t1' true
            let res = 
                let (m1give, m1get) = (valuesForAllParties currencyExchangeValue t1')
                let (m2give, m2get) = (valuesForAllParties currencyExchangeValue t2')
                equalMap (m1give, m2give) && equalMap (m1get, m2get)
            let res = res |> (||) (parties1 = parties2)
            let res = res |> (||) (equalTransactions currencyExchangeValue t1 t2)
            let res = res |> (||) (exactEqualTransaction currencyExchangeValue t1 t2)
            let res = res |> (||) (equalNegativeContract currencyExchangeValue t1' t2')
            res        
        | None, None -> true
        | _ -> false
     
    let t1 = eval c1 obs, eval c2 obs
    let t2 = evalMapParty c1 obs, evalMapParty c2 obs
    (allProperties t1 ) && (allProperties t2 )

let duration f args= 
    let timer = new System.Diagnostics.Stopwatch()
    timer.Start()
    let returnValue = f args
    printfn "Elapsed Time: %i" timer.ElapsedMilliseconds
    returnValue 

[<EntryPoint>]
let main argv =
    let obsEnv = emptyObsEnv ()
    printfn "Test=%A" (evalConFromT testX     0 obsEnv (TransactionsMapDay Map.empty)                 generateRealObs generateBoolObs)
    printfn "obsEnv=%A" obsEnv



    printfn "Test=%A" (evalConFromT testRec     0 (emptyObsEnv ()) (TransactionsMapDay Map.empty)                 generateFloatObsFromConsole generateBoolObsFromConsole)
    printfn "Test=%A" (evalConFromT testIterCon 0 (emptyObsEnv ()) (TransactionsMapParty (Map.empty, Map.empty))  generateFloatObsFromConsole generateBoolObsFromConsole)
    //printfn "Test=%A" (evalConFromT test9       0 (emptyObsEnv ()) (TransactionsMapDay Map.empty)                generateFloatObsFromConsole generateBoolObsFromConsole)
            
    let ammount = 100
    let lstRandomC = [1..ammount] |> List.map(fun _ -> randomContract 0)
    printfn "Done generating %A random contracts" ammount
    printfn "Start evaluating"

    duration (fun lst -> lst |> List.map(fun con -> evalConFromT con 0 (emptyObsEnv ()) (TransactionsMapDay Map.empty) generateRealObs generateBoolObs) ) lstRandomC
    |> ignore
    printfn "Set test9:"
    duration (fun lst -> lst |> List.map(fun con -> setOfObservables test9) ) lstRandomC |> ignore

    printfn "Set test23:"
    duration (fun lst -> lst |> List.map(fun con -> setOfObservables test23) ) lstRandomC |> ignore

    //printfn "Set testcon:"
    //duration (fun lst -> lst |> List.map(fun con -> setOfObservables con) ) lstRandomC |> ignore

    0 // return an integer exit code
