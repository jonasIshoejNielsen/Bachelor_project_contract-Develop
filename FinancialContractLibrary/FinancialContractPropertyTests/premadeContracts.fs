module premadeContracts
    open FsCheck
    open FsCheck.Xunit
    open ContractTypes
    open ContractEval
    open ContractProperties
    open TransactionProperties
    open ContractTypeInference
    open ContractHelperFunctions
    open Generators

    let parties () = [|"x1"; "y1"; "z1"; "x1"; "y2"; "z3"|]
    let (--) a i = Array.get a i

    let equalContracts1  (p) =
        let c1 = And (createSimplePay 42.0 (p--0) (p--1), createSimplePay 42.0 (p--1) (p--0))
        let c2 = And (createSimplePay 69.0 (p--0) (p--1), createSimplePay 69.0 (p--1) (p--0))
        c1, c2
    let equalContracts2  (p) =
        let c1 = Pay (DKK, Real 10.0, 10, p--1, p--0)
        let c2 = Shift(Scale(Pay (DKK, Real 1.0, 10, p--1, p--0),Real 10.0),3)
        c1, c2
    let lessCashFlowFromFirstContract (p) =
        let andx1 = And (createSimplePay 42.0 (p--0) (p--1), createSimplePay 42.0 (p--0) (p--1))
        let andy1 = And (createSimplePay 69.0 (p--0) (p--1), createSimplePay 69.0 (p--0) (p--1))
        andx1, andy1
    let lessCashFlowFromFirstContract2 (p) =
        let r = Add(ObsReal (2, Defaults (p--1)), ObsReal (2, Exercises (p--1)))
        let andx1 = And (Pay(DKK,r, 21, (p--0), (p--1)), createSimplePay 42.0 (p--0) (p--1))
        let andy1 = And (Pay(DKK,r, 21, (p--0), (p--1)), createSimplePay 69.0 (p--0) (p--1))
        andx1, andy1
    let exactEqualContracts1  (p) =
        let one = IfUnbound ((ObsBool (2, Defaults (p--0)), createSimplePay 42.0 (p--0) (p--1)))
        let two = IfUnbound ((ObsBool (2, Defaults (p--0)), createSimplePay 42.0 (p--0) (p--1)))
        one, two
    let equalContracts3  (p) =
        let c1,c2 = equalContracts2(p)
        c1, Shift(c2, -3)
    let exactEqualContracts3  (p) =
        let c1  = 
            LetFunC ("x", ["n"],
                If (RGT(VarR "n", Real 0.0), And(Shift(CallC ("x",[VReal(Sub( VarR "n", Real 1.0))]), 10), Pay(DKK, VarR "n", 10, p--0, p--1)), Zero),
                Shift(CallC ("x",[VReal( Real 5.0 )]), 10))
        let pay r d = Pay(DKK, Real r, d, p--0, p--1)
        let c2 = And(pay 5.0 20, And(pay 4.0 30, And(pay 3.0 40, And(pay 2.0 50, pay 1.0 60 ))))
        c1,c2
    let ifWithinSingle (p) =
        let andx1, andy1 = lessCashFlowFromFirstContract (p)
        let con1 = IfWithin((ObsBool (0, Pickable(Defaults (p --0), 1))), 30, andx1, andy1)
        con1
    let ofthenEqual1 (p) =
        let andx1, _ = lessCashFlowFromFirstContract (p)
        ifWithinSingle(p), andx1
    let ofthenEqual3 (p)=
        let mostly = Pay(DKK, Real 99.9, 3, (p--1), (p--2) )
        let c1=
            LetFunB ("x", ["acc"; "val"], BOr(VarB "acc", VarB "val"), 
                If (FoldBool ("x", ObsBool (12, Exercises (p--2)), Bool false, Real 200.0, Real 12.0), mostly, Shift(mostly, 10) ))
        c1, mostly
    
    let ofthenEqual2 (p)=
        let c1, c2 = ofthenEqual3(p)
        Shift(c1, 33), c2
      
    let lessCashFlowForPartyFromFirstContracts   =
        [lessCashFlowFromFirstContract(parties()), (parties()--1);
        lessCashFlowFromFirstContract2(parties()), (parties()--1)]
    let moreCashFlowForPartyFromFirstContracts   =
        [lessCashFlowFromFirstContract(parties()), (parties()--0);
        lessCashFlowFromFirstContract2(parties()), (parties()--0);]

    let ofthenEqalForPartyContracts         =
        [ofthenEqual1(parties()), parties()--1;
        ofthenEqual2(parties()), parties()--2;
        ofthenEqual3(parties()), parties()--2]
    let ofthenEqalContracts                 =
        [ofthenEqual1(parties()), ();
        ofthenEqual3(parties()), ();
        ofthenEqual2(parties()), ();]
    let ofthenExactEqalContracts            =
        []      //todo write some
    
    
    let equalNumberOfPaysContracts           =
        [equalContracts1(parties());
        equalContracts2(parties());
        lessCashFlowFromFirstContract (parties());
        lessCashFlowFromFirstContract2(parties());
        exactEqualContracts1(parties());
        equalContracts3(parties());
        exactEqualContracts3(parties());
        ofthenEqual1(parties());
        ofthenEqual3(parties())]
        
    let equalNumberOfPaysContractsForParty  =
        [equalContracts1(parties()), (parties()--0);
        equalContracts1(parties()), (parties()--1);
        equalContracts2(parties()), (parties()--0);
        equalContracts2(parties()), (parties()--1);
        exactEqualContracts3(parties()), (parties()--0);
        exactEqualContracts3(parties()), (parties()--1)]

    let equalMaxValue           =
        [equalContracts1(parties());
        equalContracts2(parties());
        equalContracts3 (parties());
        exactEqualContracts1 (parties())]

    let eqalCashFlowBothContracts           =
        [equalContracts1(parties());
        equalContracts2(parties());
        equalContracts3 (parties());
        exactEqualContracts1 (parties());
        exactEqualContracts3 (parties())]
    let equalPartiesContracts               =
        [equalContracts1 (parties());
        equalContracts2(parties());
        exactEqualContracts1 (parties());
        exactEqualContracts3 (parties())]
    let exactEqualContracts                 =
        [ exactEqualContracts1 (parties());
        exactEqualContracts3 (parties())] 

    let predicateTestContracts             :(Contract*string*Predicate)list =
        [ifWithinSingle             (parties()),    (parties ()--1), (PredAnd( PredVal(GTV 0.0, DKK), PredDate(LTED 100)),                          ForAtleastOne);
        (fst (equalContracts1       (parties()))),  (parties ()--1), (PredAnd( PredVal(GTV 0.0, DKK), PredDate(LTED 2)),                            ForAll);
        (fst (exactEqualContracts3  (parties()))),  (parties ()--1), (PredIF(PredDate(LTED(40)), PredVal(GTEV 3.0, DKK), PredVal(LTEV 2.0, DKK) ),  ForAll);
        ifWithinSingle              (parties()),    (parties ()--1), (PredIF(PredDate(LTED(30)), PredVal(EQV 42.0, DKK), PredVal(LTEV 69.0, DKK) ), ForAll);
        (fst (exactEqualContracts3  (parties()))),  (parties ()--1), (PredVal(EQV 5.0, DKK),                                                        ForAtleastOne);
        (fst (ofthenEqual3     (parties()))),  (parties ()--1), (PredIF(PredDate(EQD(3)), PredVal(EQV 99.9, DKK), PredBool true),              ForAll)]