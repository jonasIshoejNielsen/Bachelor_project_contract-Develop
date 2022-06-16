module TestCase
    open Generators
    open ProgramTest
    open PropertyTest
    open FsCheck
    open FsCheck.Xunit
    open ContractTypes
    open ContractSimplify
    open ContractEval
    open ContractHelperFunctions
    open TransactionProperties
    open ContractRandomGenerator
    
    [<Property(Verbose = true)>]
    let ``Identical to itself`` () =
        let c1 = 
            Shift
                (Scale
                   (Shift (Pay (EURO,Real 8.0,19,"b","T"),10),
                    ObsReal (70, Defaults "H")),
                 84)
        ProgramTest.``Identical to simplify`` () c1
    
        
