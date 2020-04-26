require "substitution.k"

module LOGIC-SYNTAX
    imports DOMAINS-SYNTAX

    syntax Label ::= "main" [token]
                   | Id

    syntax Block ::= "block" Label "start" Instr "end"
    syntax SingleInstr ::= "unify" [token]
                         | "dif" [token]
                         | "pop" [token]
                         | "rot" [token]
                         | "dup" [token]
                         | "branch" Label Label
                         | "goto" Label
                         | "var" Id
                         | "int" Int
                         | "functor" String Int
    syntax Instr ::= List{SingleInstr, ";"}
    syntax Program ::= List{Block, ""}
endmodule

module LOGIC
    imports DOMAINS
    imports SUBSTITUTION

    imports LOGIC-SYNTAX

    syntax KVar ::= Id

    configuration
        <k> $PGM:Program </k>
        <blocks> .Map </blocks>
        <states> .List </states>

    // A State has an instruction list, a unification, and a stack
    syntax State ::= state(Instr, Set, List)
                   | runUnif(Instr, Set, List)
                   | checkUnif(Instr, Set, List)
    syntax Func ::= func(String, List)
    syntax KItem ::= KItem "=" KItem
                   | KItem "~=" KItem
                   | Func

    syntax Bool ::= unifDone(Set) [function]
                  | checkDone(KItem, Set) [function]
                  | isLt(KItem, KItem) [function]
                  | isFunc(KItem) [function]
                  | canUnify(KItem, Set) [function]
                  | unifPossible(Set) [function]

    syntax Set ::= vars(KItem) [function]
                 | sortUnif(Set) [function]
                 | performUnif(Set) [function]

    rule vars(S:Id) => SetItem(S)
    rule vars(I:Int) => .Set
    rule vars(.Set) => .Set
    rule vars(.List) => .Set
    rule vars(ListItem(A) L) => vars(A) vars(L)
    rule vars(func(F, Args)) => vars(Args)
    rule vars(SetItem(A = B) S) => vars(A) vars(B) vars(S)
    rule vars(SetItem(A ~= B) S) => vars(A) vars(B) vars(S)

    rule isLt(A:Id, B:Int) => true
    rule isLt(A:Id, B:Func) => true
    rule isLt(A:Int, B:Func) => true

    rule isLt(A:Int, B:Id) => false
    rule isLt(A:Func, B:Id) => false
    rule isLt(A:Func, B:Int) => false

    rule isLt(A:Id, B:Id) => Id2String(A) <String Id2String(B)
    rule isLt(A:Int, B:Int) => A <Int B

    rule isLt(func(F, ArgsF), func(G, ArgsG)) =>
         (F <String G) orBool
         (F ==String G andBool isLt(ArgsF, ArgsG))
    rule isLt(.List, .List) => false
    rule isLt(ListItem(A) As, ListItem(B) Bs) => isLt(A, B) orBool (A ==K B andBool isLt(As, Bs))

    rule sortUnif(.Set) => .Set
    rule sortUnif(SetItem(A = B) Unif) => SetItem(B = A) sortUnif(Unif)
        requires isLt(B, A)
    rule sortUnif(SetItem(A = B) Unif) => SetItem(A = B) sortUnif(Unif)
        requires notBool(isLt(B, A))
    rule sortUnif(SetItem(A ~= B) Unif) => SetItem(B ~= A) sortUnif(Unif)
        requires isLt(B, A)
    rule sortUnif(SetItem(A ~= B) Unif) => SetItem(A ~= B) sortUnif(Unif)
        requires notBool(isLt(B, A))

    rule unifPossible(.Set) => true
    rule unifPossible(SetItem(I1:Int = I2:Int) Unif) => I1 ==Int I2 andBool unifPossible(Unif)
    rule unifPossible(SetItem(A:Id ~= B) Unif) => A =/=K B andBool unifPossible(Unif)
    // If this is left over after peforming unification, then we must have failed because we would decompose if F ==K G.
    rule unifPossible(SetItem(func(F, _) = func(G, _)) Unif) => false
    rule unifPossible(SetItem(A:Id = B) Unif) =>
         notBool(A in vars(B)) andBool unifPossible(Unif)

    syntax Bool ::= sameFuncName(KItem, KItem) [function]
    rule sameFuncName(func(F, _), func(G, _)) => F ==String G
    rule sameFuncName(A:Id, _) => false
    rule sameFuncName(A:Int, _) => false

    rule unifDone(.Set) => true
    rule unifDone(SetItem(A = B) Unif) =>
         // Make sure that none of the rules apply to this equation
         A =/=K B andBool
         (notBool (A in vars(Unif) andBool B in vars(Unif))) andBool
         (notBool (sameFuncName(A, B))) andBool
         (notBool ((notBool A in vars(B)) andBool (notBool B in vars(B)) andBool (A in vars(Unif)))) andBool
         unifDone(Unif)

    rule performUnif(SetItem(A = A) Unif) => performUnif(Unif)
    rule performUnif(SetItem(X = T) (Unif => Unif[X |-> T]))
        requires
            X in vars(Unif) andBool
            (notBool X in vars(T)) andBool
            (notBool T in vars(T)) // Note this will only happen if T is a variable.
    rule performUnif(SetItem(A = B) (Unif => Unif[B |-> A]))
        requires
            A =/=K B andBool
            A in vars(Unif) andBool
            B in vars(Unif)
    rule performUnif(Unif) => Unif
        requires unifDone(Unif)

    rule
        <states>
            ListItem(runUnif(Is, Unif, Stack) => checkUnif(Is, performUnif(sortUnif(Unif)), Stack))
            ...
        </states>

    rule
        <states>
            ListItem(checkUnif(Is, Unif, Stack))
            States
            =>
            States
            ListItem(state(Is, Unif, Stack))
        </states>
        requires unifPossible(Unif)
    rule
        <states>
            ListItem(checkUnif(Is, Unif, Stack)) => .List
            ...
        </states>
        requires notBool(unifPossible(Unif))

    rule
        <k>
            .Program => .
        </k>
        <states>
            .List => ListItem(state(goto main, .Set, .List))
        </states>

    rule
        <k>
            block B:Label start
                Is:Instr
            end
            Bs:Program
            =>
            Bs
        </k>
        <blocks>
            ...
            (.Map => B |-> Is)
            ...
        </blocks>

    rule
        <blocks>
            ...
            (L |-> B)
            ...
        </blocks>
        <states>
            ListItem(state(goto L, Unif, Stack))
            Ss
            =>
            Ss
            ListItem(state(B, Unif, Stack))
        </states>

    rule
        <blocks>
            ...
            (L1 |-> B1)
            (L2 |-> B2)
            ...
        </blocks>
        <states>
            ListItem(state(branch L1 L2, Unif, Stack))
            States
            =>
            States
            ListItem(state(B1, Unif, Stack))
            ListItem(state(B2, Unif, Stack))
        </states>

    rule
        <states>
            ListItem(state((var V; Is), Unif, Stack))
            States
            =>
            States
            ListItem(state(Is, Unif, ListItem(V) Stack))
        </states>

    rule
        <states>
            ListItem(state((int I; Is), Unif, Stack))
            States
            =>
            States
            ListItem(state(Is, Unif, ListItem(I) Stack))
        </states>

    rule
        <states>
            ListItem(state((unify; Is), Unif, ListItem(A) ListItem(B) Stack))
            States
            =>
            States
            ListItem(runUnif(Is, SetItem(A = B) Unif, Stack))
        </states>

    rule
        <states>
            ListItem(state((dif; Is), Unif, ListItem(A) ListItem(B) Stack))
            States
            =>
            States
            ListItem(runUnif(Is, SetItem(A ~= B) Unif, Stack))
        </states>

    rule
        <states>
            ListItem(state((pop; Is), Unif, ListItem(A) Stack))
            States
            =>
            States
            ListItem(state(Is, Unif, Stack))
        </states>

    rule
        <states>
            ListItem(state((dup; Is), Unif, ListItem(A) Stack))
            States
            =>
            States
            ListItem(state(Is, Unif, ListItem(A) ListItem(A) Stack))
        </states>

    rule
        <states>
            ListItem(state((rot; Is), Unif, ListItem(A) Stack))
            States
            =>
            States
            ListItem(state(Is, Unif, Stack ListItem(A)))
        </states>
endmodule

