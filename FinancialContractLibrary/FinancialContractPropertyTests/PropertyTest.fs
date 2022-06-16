module PropertyTest
    open FsCheck
    open FsCheck.Xunit
    open ContractTypes
    open ContractEval
    open ContractProperties
    open TransactionProperties
    open ContractTypeInference
    open ContractHelperFunctions
    open Generators
    open premadeContracts
    open MaxValueContractsProperty

    let evalBoth xs (andx1, andy1) evalFunction=
        evalFunction andx1 0 xs, evalFunction andy1 0 xs

    
    let foldWithObs lst evalFunction f = 
        fun xs -> lst |> List.fold(fun acc (c1,c2) -> f (evalBoth xs (c1,c2) evalFunction) |> (&&) acc ) true
        |> Generators.ObsEnvGenerator

    let foldWithObsAndExtra lst evalFunction f = 
        fun xs -> lst |> List.fold(fun acc ((c1,c2),p) -> f (evalBoth xs (c1,c2) evalFunction) p |> (&&) acc ) true
        |> Generators.ObsEnvGenerator

    let foldWithCurrency lst evalFunction f = 
        fun xs -> lst |> List.fold(fun acc (c1,c2) -> f ((evalBoth (emptyObsEnv ()) (c1,c2) evalFunction), xs) |> (&&) acc ) true
        |> Generators.ArbitraryGenerator

    let foldContractWithObsAndPredicate lst f = 
        fun xs -> lst |> List.fold(fun acc (c1, p, predicate) -> f (eval c1 xs) p predicate |> (&&) acc ) true
        |> Generators.ObsEnvGenerator
    
    let foldWithObsWithoutEval lst f = 
        fun xs -> lst |> List.fold(fun acc ((c1,c2),other) -> f ((c1,c2), xs, other) |> (&&) acc ) true
        |> Generators.ObsEnvGenerator

    let foldWithCurrencyWithoutEval lst f = 
        fun xs -> lst |> List.fold(fun acc (c1,c2) -> f ((c1,c2), xs) |> (&&) acc ) true
        |> Generators.ArbitraryGenerator


    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``LessCashFlow For Party p _with random obsEnv -NoFilter`` () =
        fun (eval1,eval2) p ->
            lessCashFlow p (currencyExchangeDefault ()) eval1 eval2
        |> foldWithObsAndExtra lessCashFlowForPartyFromFirstContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``not LessCashFlow For Party p _with random obsEnv -NoFilter`` () =
        fun (eval1,eval2) p ->
            lessCashFlow p (currencyExchangeDefault ()) eval1 eval2 |>not
        |> foldWithObsAndExtra moreCashFlowForPartyFromFirstContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Transactions with random obsEnv _with random obsEnv -NoFilter`` () =
        fun (eval1,eval2) ->
            equalTransactions (currencyExchangeDefault ()) eval1 eval2
        |> foldWithObs eqalCashFlowBothContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Transactions _with random Currencies -NoFilter`` () =
        fun ((eval1,eval2),cExchange) ->
            equalTransactions cExchange eval1 eval2
        |> foldWithCurrency eqalCashFlowBothContracts evalFromTMapParty
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays in evalFromTMapParty _with random obsEnv -NoFilter`` () =
        fun (eval1,eval2) ->
            equalNumberOfPays eval1 eval2
        |> foldWithObs equalNumberOfPaysContracts evalFromTMapParty
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays in evalFromTMapDay _with random obsEnv -NoFilter`` () =
        fun (eval1,eval2) ->
            equalNumberOfPays eval1 eval2
        |> foldWithObs equalNumberOfPaysContracts evalFromTMapDay
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays For Party p in evalFromTMapParty _with random obsEnv -NoFilter`` () =
        fun (eval1,eval2) p ->
            equalNumberOfPaysForParty p eval1 eval2
        |> foldWithObsAndExtra equalNumberOfPaysContractsForParty evalFromTMapParty
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays For Party p in evalFromTMapDay _with random obsEnv -NoFilter`` () =
        fun (eval1,eval2) p ->
            equalNumberOfPaysForParty p eval1 eval2
        |> foldWithObsAndExtra equalNumberOfPaysContractsForParty evalFromTMapDay


    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Max Value _with random currency -NoFilter`` () =
        fun ((c1,c2),cExchange) ->
            setOfParties c1 |> Set.union (setOfParties c2 )
            |> foldMaxValue c1 c2 cExchange true
        |> foldWithCurrencyWithoutEval equalMaxValue

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Exact Equal Transaction _with random obsEnv -NoFilter`` () =
        fun (eval1,eval2) ->
            exactEqualTransaction (currencyExchangeDefault ()) eval1 eval2
        |> foldWithObs exactEqualContracts evalFromTMapDay

    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Parties Count Pay Zero_with random obsEnv -NoFilter`` () =
        fun (eval1,eval2) ->
            equalPartiesTransactions eval1 eval2 true
        |> foldWithObs equalPartiesContracts evalFromTMapParty
        
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Parties Don't Count Pay Zero _with random obsEnv -NoFilter`` () =
        fun (eval1,eval2) ->
            equalPartiesTransactions eval1 eval2 false
        |> foldWithObs equalPartiesContracts evalFromTMapParty


    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Exact Equal Transactions _with random currency -NoFilter`` () =
        fun ((eval1,eval2),cExchange) ->
            exactEqualTransaction cExchange eval1 eval2
        |> foldWithCurrency exactEqualContracts evalFromTMapDay

    [<Property(Verbose = true)>]
    let ``PredicateTests _with random obsEnv -NoFilter`` () =
        fun eval p predicate ->
            (evalPredicateTest eval p predicate (currencyExchangeDefault()))
        |> foldContractWithObsAndPredicate predicateTestContracts

    let OftenEqualFunctions lst evalFunction f =
        fun ((c1,c2), xs, p) ->
            let rec aux xs failed =
                let xsReal, xsBool = xs.realObsEnv, xs.boolObsEnv
                let eval1, eval2 = evalBoth xs (c1,c2) evalFunction
                let res = p |> f eval1 eval2
                if (not res) && failed < 3
                then 
                    xs.realObsEnv <- xsReal
                    xs.boolObsEnv <- xsBool
                    aux xs (failed+1) 
                else res
            aux xs 0
        |> foldWithObsWithoutEval lst

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Ofthen Equal _with random obsEnv -NoFilter`` () =
        fun eval1 eval2 _ -> equalTransactions (currencyExchangeDefault ()) eval1 eval2
        |> OftenEqualFunctions ofthenEqalContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Ofthen Equal For One Party _with random obsEnv -NoFilter`` () =
        fun eval1 eval2 p -> equalCashFlow p (currencyExchangeDefault ()) eval1 eval2
        |> OftenEqualFunctions ofthenEqalForPartyContracts evalFromTMapParty
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Ofthen Exact Equal _with random obsEnv -NoFilter`` () =
        fun eval1 eval2 _ -> exactEqualTransaction (currencyExchangeDefault ()) eval1 eval2
        |> OftenEqualFunctions ofthenExactEqalContracts evalFromTMapDay





        
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``LessCashFlow For Party p _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun (eval1,eval2) p ->
            lessCashFlow p (currencyExchangeDefault ()) (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> foldWithObsAndExtra lessCashFlowForPartyFromFirstContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``not LessCashFlow For Party p _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun (eval1,eval2) p ->
            lessCashFlow p (currencyExchangeDefault ()) (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays) |>not
        |> foldWithObsAndExtra moreCashFlowForPartyFromFirstContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Transactions with random obsEnv _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun (eval1,eval2) ->
            equalTransactions (currencyExchangeDefault ()) (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> foldWithObs eqalCashFlowBothContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Transactions _with random Currencies -transactionsWithoutZeroPays`` () =
        fun ((eval1,eval2),cExchange) ->
            equalTransactions cExchange (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> foldWithCurrency eqalCashFlowBothContracts evalFromTMapParty
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays in evalFromTMapParty _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun (eval1,eval2) ->
            equalNumberOfPays (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> foldWithObs equalNumberOfPaysContracts evalFromTMapParty
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays in evalFromTMapDay _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun (eval1,eval2) ->
            equalNumberOfPays (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> foldWithObs equalNumberOfPaysContracts evalFromTMapDay
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays For Party p in evalFromTMapParty _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun (eval1,eval2) p ->
            equalNumberOfPaysForParty p (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> foldWithObsAndExtra equalNumberOfPaysContractsForParty evalFromTMapParty
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays For Party p in evalFromTMapDay _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun (eval1,eval2) p ->
            equalNumberOfPaysForParty p (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> foldWithObsAndExtra equalNumberOfPaysContractsForParty evalFromTMapDay


    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Max Value _with random currency -transactionsWithoutZeroPays`` () =
        fun ((c1,c2),cExchange) ->
            setOfParties c1 |> Set.union (setOfParties c2 )
            |> foldMaxValue c1 c2 cExchange true
        |> foldWithCurrencyWithoutEval equalMaxValue

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Exact Equal Transaction _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun (eval1,eval2) ->
            exactEqualTransaction (currencyExchangeDefault ()) (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> foldWithObs exactEqualContracts evalFromTMapDay

    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Parties Count Pay Zero_with random obsEnv -transactionsWithoutZeroPays`` () =
        fun (eval1,eval2) ->
            equalPartiesTransactions (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays) true
        |> foldWithObs equalPartiesContracts evalFromTMapParty
        
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Parties Don't Count Pay Zero _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun (eval1,eval2) ->
            equalPartiesTransactions (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays) false
        |> foldWithObs equalPartiesContracts evalFromTMapParty


    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Exact Equal Transactions _with random currency -transactionsWithoutZeroPays`` () =
        fun ((eval1,eval2),cExchange) ->
            exactEqualTransaction cExchange (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> foldWithCurrency exactEqualContracts evalFromTMapDay

    [<Property(Verbose = true)>]
    let ``PredicateTests _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun eval p predicate ->
            (evalPredicateTest (eval|> transactionsWithoutZeroPays) p predicate (currencyExchangeDefault()))
        |> foldContractWithObsAndPredicate predicateTestContracts

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Ofthen Equal _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun eval1 eval2 _ -> equalTransactions (currencyExchangeDefault ()) (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> OftenEqualFunctions ofthenEqalContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Ofthen Equal For One Party _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun eval1 eval2 p -> equalCashFlow p (currencyExchangeDefault ()) (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> OftenEqualFunctions ofthenEqalForPartyContracts evalFromTMapParty
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Ofthen Exact Equal _with random obsEnv -transactionsWithoutZeroPays`` () =
        fun eval1 eval2 _ -> exactEqualTransaction (currencyExchangeDefault ()) (eval1|>transactionsWithoutZeroPays) (eval2|>transactionsWithoutZeroPays)
        |> OftenEqualFunctions ofthenExactEqalContracts evalFromTMapDay




        
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``LessCashFlow For Party p _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun (eval1,eval2) p ->
            lessCashFlow p (currencyExchangeDefault ()) (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> foldWithObsAndExtra lessCashFlowForPartyFromFirstContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``not LessCashFlow For Party p _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun (eval1,eval2) p ->
            lessCashFlow p (currencyExchangeDefault ()) (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee) |>not
        |> foldWithObsAndExtra moreCashFlowForPartyFromFirstContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Transactions with random obsEnv _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun (eval1,eval2) ->
            equalTransactions (currencyExchangeDefault ()) (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> foldWithObs eqalCashFlowBothContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Transactions _with random Currencies -transactionsWithoutPayToPayee`` () =
        fun ((eval1,eval2),cExchange) ->
            equalTransactions cExchange (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> foldWithCurrency eqalCashFlowBothContracts evalFromTMapParty
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays in evalFromTMapParty _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun (eval1,eval2) ->
            equalNumberOfPays (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> foldWithObs equalNumberOfPaysContracts evalFromTMapParty
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays in evalFromTMapDay _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun (eval1,eval2) ->
            equalNumberOfPays (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> foldWithObs equalNumberOfPaysContracts evalFromTMapDay
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays For Party p in evalFromTMapParty _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun (eval1,eval2) p ->
            equalNumberOfPaysForParty p (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> foldWithObsAndExtra equalNumberOfPaysContractsForParty evalFromTMapParty
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Number Of Pays For Party p in evalFromTMapDay _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun (eval1,eval2) p ->
            equalNumberOfPaysForParty p (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> foldWithObsAndExtra equalNumberOfPaysContractsForParty evalFromTMapDay


    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Max Value _with random currency -transactionsWithoutPayToPayee`` () =
        fun ((c1,c2),cExchange) ->
            setOfParties c1 |> Set.union (setOfParties c2 )
            |> foldMaxValue c1 c2 cExchange true
        |> foldWithCurrencyWithoutEval equalMaxValue

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Exact Equal Transaction _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun (eval1,eval2) ->
            exactEqualTransaction (currencyExchangeDefault ()) (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> foldWithObs exactEqualContracts evalFromTMapDay

    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Parties Count Pay Zero_with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun (eval1,eval2) ->
            equalPartiesTransactions (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee) true
        |> foldWithObs equalPartiesContracts evalFromTMapParty
        
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Equal Parties Don't Count Pay Zero _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun (eval1,eval2) ->
            equalPartiesTransactions (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee) false
        |> foldWithObs equalPartiesContracts evalFromTMapParty


    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Exact Equal Transactions _with random currency -transactionsWithoutPayToPayee`` () =
        fun ((eval1,eval2),cExchange) ->
            exactEqualTransaction cExchange (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> foldWithCurrency exactEqualContracts evalFromTMapDay

    [<Property(Verbose = true)>]
    let ``PredicateTests _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun eval p predicate ->
            (evalPredicateTest (eval|> transactionsWithoutPayToPayee) p predicate (currencyExchangeDefault()))
        |> foldContractWithObsAndPredicate predicateTestContracts

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Ofthen Equal _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun eval1 eval2 _ -> equalTransactions (currencyExchangeDefault ()) (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> OftenEqualFunctions ofthenEqalContracts evalFromTMapParty

    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Ofthen Equal For One Party _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun eval1 eval2 p -> equalCashFlow p (currencyExchangeDefault ()) (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> OftenEqualFunctions ofthenEqalForPartyContracts evalFromTMapParty
    
    [<Property(Verbose = true, MaxTest = 500)>]
    let ``Ofthen Exact Equal _with random obsEnv -transactionsWithoutPayToPayee`` () =
        fun eval1 eval2 _ -> exactEqualTransaction (currencyExchangeDefault ()) (eval1|>transactionsWithoutPayToPayee) (eval2|>transactionsWithoutPayToPayee)
        |> OftenEqualFunctions ofthenExactEqalContracts evalFromTMapDay

