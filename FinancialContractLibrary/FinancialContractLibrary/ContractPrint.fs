module ContractPrint
    open ContractTypes
    open System.Text
    let CurrencyToString c = match c with | DKK -> "DKK" | USD -> "USD" | EURO -> "EURO"
    let DateToString d = "day " + string(d)
    let rec LabelToString con =
        match con with 
        | Defaults p -> "Party " + p + " Defaults"
        | Exercises p -> "Party " + p + " Exercises"
        | Business cur -> "Business for currency " + (CurrencyToString cur)
        | Pickable (l, i) -> "Number " + string i + (LabelToString con)
        | Action s        -> "done action " + s
    
    let stringBuilderToSting (sb:StringBuilder) = sb.ToString ()
    let AppendStringBuilder sb lst = 
        lst |> List.fold (fun (acc:StringBuilder) (s:string) -> acc.Append s) sb
        
    let ListToString lst = AppendStringBuilder (StringBuilder ()) lst |> stringBuilderToSting
    
    let unpack1Val aux c v1 start ending    = aux v1 (fun v1 -> [start; v1; ending;] |> ListToString |> c)
    let unpack2Val aux c c1 c2 start middle = aux c1 (fun v1 -> aux c2 (fun v2 ->  [start; v1; middle; v2] |> ListToString  |> c))

    let argsToString args = (List.length args).ToString ()  //todo


    let RealToString r =
        let rec aux r c =
            let unpack1Val = unpack1Val aux c
            let unpack2Val = unpack2Val aux c
            match r with 
            | Real r                    -> r.ToString () |> c
            | Add (c1, c2)              -> unpack2Val c1 c2 "add " " with "
            | Sub (c1, c2)              -> unpack2Val c1 c2 "subtract " " with "
            | Max (c1, c2)              -> unpack2Val c1 c2 "max value of " " and "
            | Mul (c1, c2)              -> unpack2Val c1 c2 "multiply " " with "
            | Pow (v1, f)               -> unpack1Val v1 "" (" with power of " + f.ToString ())
            | ObsReal (d,c1)            -> ["("; (LabelToString c1); " "; (DateToString d); ")"]  |> ListToString  |> c
            | FoldReal(n,v, acc, i, di) -> ["Run funciton "; n; " "; i.ToString (); " times with "; di.ToString (); " days different per time starting with "; aux acc id; " and second argument "; aux v id   ]  |> ListToString  |> c
            | VarR n                    -> n |> c
            | CallR (n,args)            -> [n;"("; argsToString args; ")"] |> ListToString |> c
        aux r id
        
    let BoolToString b =
        let rec aux b c =
            let unpack1Val = unpack1Val aux c
            let unpack2Val = unpack2Val aux c
            let unpack2Real c1 c2 middle = [RealToString c1; middle; RealToString c2] |> ListToString |> c 
            
            match b with 
            | Bool b                    -> b.ToString () |> c
            | ObsBool (d,c1)            -> ["("; (LabelToString c1); " "; (DateToString d); ")"]  |> ListToString  |> c
            | BAnd (c1,c2)              -> unpack2Val c1 c2 "" " and "
            | BOr  (c1,c2)              -> unpack2Val c1 c2 "" " or "
            | BNot v1                   -> unpack1Val v1 "not " ""
            | RLT (c1, c2)              -> unpack2Real c1 c2 " less than "
            | RGT (c1, c2)              -> unpack2Real c1 c2 " greter than "
            | REQ (c1, c2)              -> unpack2Real c1 c2 " equal "
            | RLTEQ (c1, c2)            -> unpack2Real c1 c2 " less than equal "
            | RGTEQ (c1, c2)            -> unpack2Real c1 c2 " greater than equal "
            | BoolIf (v1, v2, v3)       -> aux v1 (fun v1 -> aux v2 (fun v2 -> aux v3 (fun v3 -> [" if "; v1; " then "; v2; " else "; v3] |> ListToString |> c)))
            | FoldBool(n,v,acc,i,di)    -> ["Run funciton "; n; " "; i.ToString (); " times with "; di.ToString (); " days different per time starting with "; aux acc id; " and second argument "; aux v id   ]  |> ListToString |> c
            | VarB n                    -> n |> c
            | CallB (n,args)            -> [n;"("; argsToString args; ")"] |> ListToString |> c
        aux b id
    let ContractPrint c = 
        let rec print con indent c =
            let ind () = String.replicate indent "  "
            match con with
                | Zero                      -> "Ø" |> c
                | Pay (cur, i, d, fp, tp)   -> [fp; " pay: "; RealToString i; " "; CurrencyToString cur; " to "; tp; " at: ";  DateToString d] |> ListToString |> c
                | And (c1, c2)              -> print c1 indent (fun v1-> print c2 indent (fun v2-> ["("; v1; ind (); "and "; v2; ")"]  |> ListToString |> c))
                | Scale(c1, i)              -> print c1 indent (fun v1-> ["Scaled ("; v1; ") with: "; string i] |> ListToString |> c)
                | Shift(c1,d)               -> print c1 indent (fun v1-> ["Extend ("; v1; ") with: "; DateToString d] |> ListToString |> c)
                | If(ob,c1,c2)              -> print c1 (indent+1) (fun v1-> print c2 (indent+1) (fun v2-> ["if "; BoolToString ob; " \n"; ind (); "then "; v1; " \n"; ind (); "else "; v2]  |> ListToString |> c))
                | IfUnbound(ob, c1)         -> print c1 (indent+1) (fun v1-> ["if "; BoolToString ob; " happens "; " \n"; ind (); "then "; v1; " \n"; ] |> ListToString |> c)
                | IfWithin(ob, d, c1, c2)   -> print c1 (indent+1) (fun v1-> print c2 (indent+1) (fun v2-> ["if "; BoolToString ob; " happens within "; DateToString d; " \n"; ind (); "then "; v1; " \n"; ind (); "else "; v2]  |> ListToString |> c))
                | VarC n                    -> n |> c
                | LetR(n, eRhs, eBody)      -> print eBody indent (fun v1-> ["let "; n; " = "; (RealToString eRhs); " in ("; v1; ")";] |> ListToString |> c)
                | LetB(n, eRhs, eBody)      -> print eBody indent (fun v1-> ["let "; n; " = "; (BoolToString eRhs); " in ("; v1; ")";] |> ListToString |> c)
                | LetC(n, eRhs, eBody)      -> print eBody indent (fun v1-> print eRhs indent (fun eRhs -> ["let "; n; " = "; eRhs; " in ("; v1; ")";] |> ListToString |> c))
                | LetFunC(n, args, eRhs, eBody) -> print eBody indent (fun v1 -> print eRhs indent (fun v2 -> ["let "; n; "("; args.ToString (); ") = "; v2; " in ("; v1; ")";] |> ListToString |> c))
                | LetFunB(n, args, eRhs, eBody) -> print eBody indent (fun v1 -> ["let "; n; "("; args.ToString (); ") = "; BoolToString eRhs ; " in ("; v1; ")";] |> ListToString |> c)
                | LetFunR(n, args, eRhs, eBody) -> print eBody indent (fun v1 -> ["let "; n; "("; args.ToString (); ") = "; RealToString eRhs ; " in ("; v1; ")";] |> ListToString |> c)
                | IterCon(n, v, i, di)          -> print v     indent (fun v1 -> ["Run funciton "; n; " "; i.ToString (); " times with "; di.ToString (); " days different per time with argument "; v1   ]  |> ListToString |> c)
                | CallC (n, args)           -> [n;"("; argsToString args; ")"] |> ListToString |> c
        print c 0 id


    let TransactionsPrint t = 
        match t with
        | None -> printfn "null"
        | Some tlst ->
            match tlst with
            | TransactionsDay tlst -> 
                let rec printTransaction t = 
                    match t with 
                    | [] ->()
                    | (partyFrom, partyTo, i, curr) :: tt ->
                        printfn "  - Party %s pay: %A %A to party %s" partyFrom i curr partyTo
                        printTransaction tt

                let rec print tlst : unit= 
                    match tlst with
                    | [] -> ()
                    | (i, t)::tt -> printfn "On Day %d" i; printTransaction t; print tt
                print tlst
            | TransactionsParty (tlst, _) -> 
                let rec printTransaction (t: (int*Transaction) list) = 
                    match t with 
                    | [] ->()
                    | (d, (partyFrom, partyTo, i, curr)) :: tt ->
                        printfn "  - On Day %d Party %s pay: %A %A to party %s" d partyFrom i curr partyTo
                        printTransaction tt
            
                let rec print tlst : unit= 
                    match tlst with
                    | [] -> ()
                    | (i, t)::tt -> printfn "For party %s" i; printTransaction t; print tt
            
                print tlst

