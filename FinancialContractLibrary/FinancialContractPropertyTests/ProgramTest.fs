module ProgramTest 
    open FsCheck
    open FsCheck.Xunit
    open ContractTypes
    open ContractEval
    open ContractProperties
    open TransactionProperties
    open ContractTypeInference
    open ContractHelperFunctions
    open Generators
    open PropertyTest
    open ContractSimplify
    
    ///<summary>Test that 2 contracts are equal for all properties</summary>
    let identical currencyExchangeValue c1 c2 = 
        let obs = emptyObsEnv ()
        if unBoundTestCon c1 && unBoundTestCon c2 && typ c1 && typ c2 
        then
            let (t11, t12) = eval c1 obs, eval c2 obs
            let (t21, t22) = evalMapParty c1 obs, evalMapParty c2 obs
            (allProperties currencyExchangeValue (t11, t12) )
            >>= fun _ -> (allProperties currencyExchangeValue (t21, t22) ) 
            >>= fun _ -> (allProperties currencyExchangeValue (t11 |> transactionsWithoutZeroPays, t12 |> transactionsWithoutZeroPays) ) 
            >>= fun _ -> (allProperties currencyExchangeValue (t21 |> transactionsWithoutZeroPays, t22 |> transactionsWithoutZeroPays) ) 
            >>= fun _ -> (allProperties currencyExchangeValue (t11 |> transactionsWithoutPayToPayee, t12 |> transactionsWithoutPayToPayee) ) 
            >>= fun _ -> (allProperties currencyExchangeValue (t21 |> transactionsWithoutPayToPayee, t22 |> transactionsWithoutPayToPayee) ) 
        else true

    [<Property(Verbose = true, MaxTest = 100)>]
    let ``Identical to itself`` () =
        fun (c1) -> identical (currencyExchangeDefault ()) c1 c1
        |> ArbitraryGenerator
    
    [<Property(Verbose = true, MaxTest = 100)>]
    let ``Identical to simplify`` () =
        fun (c1) -> identical (currencyExchangeDefault ()) c1 (simplifyC c1)
        |> ArbitraryGenerator
    
    [<Property(Verbose = true, MaxTest = 100)>]
    let ``Identical to double negation`` () =
        fun (c1) ->
            let exChangeDefault = (currencyExchangeDefault ())
            c1 |> (genNegateValueContract >> genNegateValueContract >> identical exChangeDefault c1)
        |> ArbitraryGenerator

    [<Property(Verbose = true, MaxTest = 100)>]
    let ``Identical to double switched`` () =
        fun (c1) ->
            let exChangeDefault = (currencyExchangeDefault ())
            c1 |> (genSwitchedContract >> genSwitchedContract >> identical exChangeDefault c1)
        |> ArbitraryGenerator
    
    [<Property(Verbose = true, MaxTest = 100)>]
    let ``Identical to itself with random Currency`` () =
        fun c1 cExcahange -> identical cExcahange c1 c1
        |> ArbitraryGenerator
    [<Property(Verbose = true, MaxTest = 100)>]
    let ``Identical of taking twice to scale with two`` () =
        fun (c1) -> identical (currencyExchangeDefault ()) (And(c1,c1)) (Scale(c1, Real 2.0))
        |> ArbitraryGenerator

    

    [<Property(Verbose = true, MaxTest = 100)>]
    let ``equalParties to itself`` () =
        fun (c1) -> equalParties c1 c1
        |> ArbitraryGenerator
    
    [<Property(Verbose = true, MaxTest = 100)>]
    let ``equalParties to double negation`` () =
        fun (c1) ->
            c1 |> (genNegateValueContract >> genNegateValueContract >> equalParties c1)
        |> ArbitraryGenerator

    [<Property(Verbose = true, MaxTest = 100)>]
    let ``equalParties to double switched`` () =
        fun (c1) ->
            c1 |> (genSwitchedContract >> genSwitchedContract >> equalParties c1)
        |> ArbitraryGenerator
    
    [<Property(Verbose = true, MaxTest = 100)>]
    let ``equalParties of taking twice to scale with two`` () =
        fun (c1) -> equalParties (And(c1,c1)) (Scale(c1, Real 2.0))
        |> ArbitraryGenerator

    [<Property(Verbose = true, MaxTest = 100)>]
    let ``equalMaxValue to itself`` () =
        fun (c1) -> equalMaxValue (currencyExchangeDefault ()) c1 c1
        |> ArbitraryGenerator
    
    [<Property(Verbose = true, MaxTest = 100)>]
    let ``equalMaxValue to double negation`` () =
        fun (c1) ->
            let exChangeDefault = (currencyExchangeDefault ())
            c1 |> (genNegateValueContract >> genNegateValueContract >> equalMaxValue exChangeDefault  c1)
        |> ArbitraryGenerator

    [<Property(Verbose = true, MaxTest = 100)>]
    let ``equalMaxValue to double switched`` () =
        fun (c1) ->
            let exChangeDefault = (currencyExchangeDefault ())
            c1 |> (genSwitchedContract >> genSwitchedContract >> equalMaxValue exChangeDefault c1)
        |> ArbitraryGenerator
    
    [<Property(Verbose = true, MaxTest = 100)>]
    let ``equalMaxValue to itself with random Currency`` () =
        fun c1 cExcahange -> equalMaxValue cExcahange c1 c1
        |> ArbitraryGenerator
    [<Property(Verbose = true, MaxTest = 100)>]
    let ``equalMaxValue of taking twice to scale with two`` () =
        fun (c1) -> equalMaxValue (currencyExchangeDefault ()) (And(c1,c1)) (Scale(c1, Real 2.0))
        |> ArbitraryGenerator






