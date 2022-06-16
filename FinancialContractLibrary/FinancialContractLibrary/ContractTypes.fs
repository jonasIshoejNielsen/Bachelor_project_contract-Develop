module ContractTypes
    
    type Currency =
        | DKK
        | USD
        | EURO
    type Date = int
    type Party = string

    type TypeInferenceType = 
        | TypB
        | TypR
        | TypC

    type Label =
        | Defaults      of Party
        | Exercises     of Party
        | Business      of Currency
        | Pickable      of Label * int
        | Action        of string
    type Observable = Date * Label
    type Real =
        | Real                  of float    
        | Add                   of Real   * Real
        | Sub                   of Real   * Real
        | Mul                   of Real   * Real
        | Max                   of Real   * Real
        | Pow                   of Real   * float
        | ObsReal               of Observable 
        | FoldReal              of string * Real * Real * Real * Real       //FoldReal(n,v,acc, number of iterations, shift between iterations)  calls n(acc, v)
        | VarR                  of string
        | CallR                 of string * value list
    and Bool =    
        | Bool                  of bool
        | BAnd                  of Bool   * Bool
        | BOr                   of Bool   * Bool
        | BNot                  of Bool
        | RLT                   of Real   * Real
        | RGT                   of Real   * Real
        | REQ                   of Real   * Real
        | RLTEQ                 of Real   * Real
        | RGTEQ                 of Real   * Real
        | ObsBool               of Observable
        | BoolIf                of Bool   * Bool * Bool
        | FoldBool              of string * Bool * Bool * Real * Real       //function n(acc, v), v, acc, number of iterations, shift between iterations
        | VarB                  of string
        | CallB                 of string * value list
    and Contract = 
        | Zero                                                              //NONE
        | Pay           of Currency * Real * Date * Party * Party           //pay: real currency on date from party1 to party2
        | And           of Contract * Contract                              //And: do both
        | Scale         of Contract * Real                                  //Scale: multiply timeextend with real
        | Shift         of Contract * Date                                  //Shift: move date forward in time
        | If            of Bool * Contract * Contract
        | IfWithin      of Bool * Date * Contract * Contract
        | IfUnbound     of Bool * Contract
        | LetR          of string * Real * Contract
        | LetB          of string * Bool * Contract
        | LetC          of string * Contract * Contract
        | LetFunC       of string * string list * Contract * Contract
        | LetFunB       of string * string list * Bool * Contract
        | LetFunR       of string * string list * Real * Contract
        | IterCon       of string * Contract * Real * Real       //function n(v), v, number of iterations, shift between iterations
        | VarC          of string
        | CallC         of string * value list
    and value = | VReal of Real | VBool of Bool | VCon  of Contract

    type Transaction  =  (Party * Party * float * Currency)                 //Transaction: float currency from party1 to party2
    type PartyTransactions = (Party * (Date * Transaction) list) list       //PartyTransactions: list of a (party and a list of (date*transactions))
    type Transactions = 
        | TransactionsDay       of (Date * Transaction list) list           //TransactionsDay: list of (date*transactions)
        | TransactionsParty     of PartyTransactions * PartyTransactions    //TransactionsParty: tuple of TransactionsParty, with first PartyTransactions with party paying and second PartyTransactions with party receiving

    type TransactionsMap = 
        | TransactionsMapDay    of Map<Date, Transaction list>
        | TransactionsMapParty  of Map<Party, (Date * Transaction) list> * Map<Party, (int * Transaction) list>
    
    
    type ObsEnv = {mutable count:  int option; mutable boolObsEnv:  Map<Observable, bool>;  mutable realObsEnv: Map<Observable, float>}
    
    type letEnvironment =
        | MapReal       of Map<string, LetType<Real>>
        | MapBool       of Map<string, LetType<Bool>> * Map<string, LetType<Real>>
        | MapContract   of Map<string, LetType<Bool>> * Map<string, LetType<Real>> * Map<string, LetType<Contract>>
    and LetType<'a> = 
        | Variable of 'a
        | Closure  of string list * 'a * letEnvironment


    exception ObservableNotFound of Label*Date
        with override this.Message =  match this :> exn with | ObservableNotFound(l,d)  -> sprintf "(Couldn't find: %A at day: %A)" l d | _ -> sprintf ""
    exception UnBoundException of string * string
        with override this.Message =  match this :> exn with | UnBoundException(n,msg)  -> sprintf "%A was unbound, but expected an bound: %s)" n msg | _ -> sprintf ""
    exception ReferencedFunctionExpectedVar of string
    exception ReferencedVarExpectedFunction of string

    type ValPredicate =
    | EQV   of float
    | GTV   of float
    | GTEV  of float
    | LTV   of float
    | LTEV  of float

    type DatePredicate =
    | EQD   of Date
    | GTD   of Date
    | GTED  of Date
    | LTD   of Date
    | LTED  of Date

    type Condition = 
    | PredVal   of ValPredicate*Currency
    | PredDate  of DatePredicate
    | PredAnd   of Condition*Condition
    | PredIF    of Condition*Condition*Condition
    | PredOr    of Condition*Condition
    | PredNot   of Condition
    | PredBool  of bool

    type ForHowMany =
    | ForAll
    | ForAtleastOne
    | ForI          of int

    type Predicate = Condition*ForHowMany

    let createAccValFunc n funT eRhs c = LetFunB (n, ["acc"], eRhs, c )
    let addLibraryFunctions =
        fun c -> LetR("pi", System.Math.PI |> Real, c )
        << fun c -> LetFunR("abs",      ["val"],            Max(VarR "val", Mul(VarR "val", Real -1.0)), c )
        << fun c -> LetFunR("max",      ["val"; "val2"],    Max(VarR "val", VarR "val2"), c )
        << fun c -> LetFunR("min",      ["val"; "val2"],    Mul(Max(Mul(VarR "val", Real -1.0), Mul(VarR "val2", Real -1.0)), Real -1.0), c )
        << fun c -> LetFunR("sum",      ["val"; "val2"],    Add(VarR "val", VarR "val"), c )
        << fun c -> LetFunR("sumAll",   ["val"; "i"; "di"], FoldReal("sum", VarR "val", Real (0.0), VarR "i", VarR "di"), c )
        << fun c -> LetFunR("div",      ["val"; "val2"],    Mul(VarR "val", Pow(VarR "val2", -1.0)) , c )
        << fun c -> LetFunR("avg",      ["val"; "i"; "di"], CallR ("div", [FoldReal("sum", VarR "val", Real (0.0), VarR "i", VarR "di") |> VReal; VarR "i" |> VReal]) , c )
        << fun c -> LetFunR("maxAll",   ["val"; "i"; "di"], FoldReal("max", VarR "val", Real (System.Int32.MinValue |> float ), VarR "i", VarR "di"), c )
        << fun c -> LetFunR("minAll",   ["val"; "i"; "di"], FoldReal("min", VarR "val", Real (System.Int32.MaxValue |> float ), VarR "i", VarR "di"), c )
        << fun c -> LetFunB("and",      ["val"; "val2"],    BAnd(VarB "val", VarB "val2"), c )
        << fun c -> LetFunB("or",       ["val"; "val2"],    BOr(VarB "val", VarB "val2"), c)
        << fun c -> LetFunB("allTrue",  ["val"; "i"; "di"], FoldBool("and", VarB "val", Bool true, VarR "i", VarR "di"), c ) 
        << fun c -> LetFunB("exists",   ["val"; "i"; "di"], FoldBool("or", VarB "val", Bool false, VarR "i", VarR "di"),  c )
        << fun c -> LetFunB("noTrue",   ["val"; "i"; "di"], CallB ("exists", [VarB "val" |> VBool; VarR "di" |> VReal; VarR "i" |> VReal]) |> BNot , c )
    





    let createBoolObs condition date =  ObsBool (date, condition)
    let createSimplePay real part1 part2 = Pay (DKK, Real real, 0, part1, part2)

    let test1 =  And (Zero, Zero)
    let test2 =  And (test1, test1)
    let test3 =  Shift (Pay (DKK, Real 2.0, (28), "x", "y") , 10)
    let test4 =  IfWithin (Bool true, 28, test2, test3)
    let test5 =  Scale (Scale (test1, Real 2.0), Real 10.0)
    let test6 =  Shift (Scale (test1, Real 2.0), 10)
    let test7 =  And (Pay (DKK, Real 42.0, 1, "me", "you"), Pay (DKK, Real 42.0, 1, "you", "me"))
    let test69 =  And (Pay (DKK, Real 42.0, 0, "me", "you"), Pay (DKK, Real 42.0, 0, "you", "me"))
    let test8 =  And (And (Pay (DKK, Real 42.0, 3, "me", "you"), test2), Shift(test3, 5))
    let obsBool1 = BOr(createBoolObs (Pickable (Defaults "x", 1)) (2), createBoolObs (Defaults "y") (0)) |> BNot
    let test9 =  IfWithin (obsBool1, 10, Pay(DKK, Real 10000.0, 2, "y", "y2" ), Shift(If(obsBool1, Zero, Pay(DKK, Real 10.0, 12, "x", "Y" )), 10))
    let test10 = IfWithin (BAnd( obsBool1 |> BNot, obsBool1), 28, And(test3, test3), test3)
    let test11 = If (RLT (Real 0.2, Real 0.1),And(test3, test3), test3)
    let test12 = If (REQ (Real 999.0, ObsReal(666, Defaults "bob")),And(test3, test3), test3)
    let test13 = If (RLT (Real 0.1, Real 0.2), Pay (DKK,  Real 10.0, 10, "x", "y"), Pay(DKK, Real 0.0, 0, "y", "x"))
    let test14 =  And (test1, test1)
    let test666 = If (BAnd (ObsBool (2, Defaults "x"), ObsBool (3, Defaults "y")), And(test3, test3), test3)
    let test16 =  LetC("c", LetR("x", Add(Real 4.0, Real 5.0), LetB("x", REQ(VarR "x", Real 9.0), If(VarB "x", Pay(DKK, Add(Real -189.0, Mul(VarR "x", Add(VarR "x", Real 12.0))), 14, "x", "y"), Zero))), And(Shift(VarC "c", 10), VarC "c"))
    let test16E1 =  LetC("c", LetR("x", Add(Real 4.0, Real 5.0), LetB("x", REQ(VarR "x", Real 9.0), If(VarB "x", Pay(DKK, Add(Real -189.0, Mul(VarR "x", Add(VarR "x", Real 12.0))), 14, "x", "y"), Zero))), And(Shift(VarC "c", 10), VarC "x"))
    let test16E2 =  LetC("c", LetR("x", Add(Real 4.0, Real 5.0), LetB("y", REQ(VarR "x", Real 9.0), If(VarB "x", Pay(DKK, Add(Real -189.0, Mul(VarR "x", Add(VarR "x", Real 12.0))), 14, "x", "y"), Zero))), And(Shift(VarC "c", 10), VarC "c"))
    let test16E3 =  LetC("c", LetR("x", Add(Real 4.0, Real 5.0), LetB("x", REQ(VarR "y", Real 9.0), If(VarB "x", Pay(DKK, Add(Real -189.0, Mul(VarR "x", Add(VarR "x", Real 12.0))), 14, "x", "y"), Zero))), And(Shift(VarC "c", 10), VarC "c"))
    let test17  = LetFunC ("x",
                           ["k"; "v"],
                           And(VarC "k", Pay(DKK, VarR "v", 10, "x", "y")),
                           And(Shift(CallC ("x",[VCon (Pay(DKK, Real 12.2, 5, "k", "y")); VReal( Real 2.2 )]), 10), CallC ("x",[VCon (Pay(DKK, Real 999.9, 5, "y", "k")); VReal( Real 9.9 )] )))    

    let test18  = LetFunB ("x",
                    ["k"; "v"],
                    BAnd(VarB "k", RLT( VarR "v", Real 9999.666)), 
                    LetR("k", Real 999.0, If (CallB("x", [Bool true |> VBool; VarR "k" |> VReal]), Pay(DKK, VarR "k", 3, "x", "y" ), Zero ))
                 )
    let test19  = LetFunR ("x",
                    ["k"; "v"; "v2"],
                    Add(VarR "k", Mul(VarR "v",VarR "v2")),
                    Pay(DKK, CallR("x", [Real 10.0 |> VReal; Real 20.0 |> VReal; Real -1.0 |> VReal]), 4, "x", "y")
                 )
    let test20 =  LetFunB ("x",
                    ["acc"; "val"],
                    BOr(VarB "acc", ObsBool (12, Exercises "k")), 
                    If (FoldBool ("x", Bool false, Bool true, Real 100000.0, Real 12.0), Pay(DKK, Real 99.9, 3, "x", "y" ), Zero )
                  )
    
    let test21 =  LetFunR ("x",
                    ["acc"; "val"],
                    Add(VarR "acc", VarR "val"), 
                    Pay(DKK, FoldReal("x", ObsReal (12, Exercises "k"), Real 9.9, Real 100000.0, Real 12.0), 3, "x", "y" )
                  )
    
    let test22 =  And(Zero, If(BAnd(Bool true, BOr(Bool false, BOr(BAnd(Bool false, Bool true), RLT(Real 99.0, Real 9999.0)))), Pay(DKK, Add(Real 22.0, Real 19.1), 12, "x", "y"), Pay(DKK, Mul(Real 12.0, Real 19.1), 12, "k", "kk") ))
    let test23 = IfUnbound (BAnd ( obsBool1 |> BNot, obsBool1), test7)
    let testRec  = 
        LetFunC ("x", ["n"; "c"],
            If (RGT(VarR "n", Real 0.0), And(Shift(CallC ("x",[VReal(Sub( VarR "n", Real 1.0)); VCon(CallC("x", [VReal(Real 0.0); VCon( VarC "c")]))]), 10), And(Pay(DKK, VarR "n", 10, "x", "y"), Scale(VarC "c", VarR "n"))), Zero),
            
            Shift(CallC ("x",[VReal( Real 5.0 ); VCon (Pay(DKK, ObsReal( 2, Defaults "x"), 0, "x", "y"))]), 10))   

    let testIterCon =  
        LetFunC ("x", [ "val"],
            And( VarC("val"), Pay(EURO, Real 0.9, 0, "x", "y")), 
            IterCon("x", Pay(EURO, Real 0.9, 0, "x", "z"), Real 9.0, Real 10.0)
        )


    let testX = 
        Pay(DKK, FoldReal("max", ObsReal (10, Action "custommers"), Real 0.0, Real 5.0, Real 10.0), 0, "x", "y" )
        |> addLibraryFunctions