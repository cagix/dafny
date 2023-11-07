/* The Dafny Abstract Machine
 * This file specifies:
 * 1. A core language for Dafny based on Levy's fine-grain call-by-value (FG-CBV) calculus
 * 2. A CEK-machine interpreter based on the Hillerstrom-Lindley-Atkey CEK machine for FG-CBV
 * 3. Eventually, a simple type system based on FG-CBV
 * 4. Eventually, a type soundness result of the CEK-machine w.r.t. the type system
*/ 

datatype Option<A> = None | Some(value: A) {
    predicate IsFailure() { this.None? }
    function PropagateFailure(): Option<A>
        requires IsFailure() { None }
    function Extract(): A
        requires !IsFailure() { this.value }
}

class Ptr<A> {
  var deref: A
  constructor(val: A) {
    deref := val;
  }
}

datatype Val =
// G, x : A+ |- x : A+
  Var(string)
// G |- true/false : Bool
| Bool(bool)
| Int(int)
// TODO: variant types
// comps have to be terminal like in FG-CBV / unlike CBPV
| Lambda(string, Comp)
//| Tuple(map<string, Comp>)
//| Ref(Ptr<Val>)

// G |- e : D and D |- V : A+ ~> G |- V 
//type Heap = set<Ptr<Comp>>

datatype Comp =
// Intro & Elim for Up(A+)
  Pure(Val)
| Bind(lhs: Comp, var_: string, rhs: Comp)
// Elim for bools
| Ite(guard: Val, then_: Comp, else_: Comp)
// Intro & Elim for arrows
| Func(bound: string, body: Comp)
| Call(func: Comp, arg: Val)
// Intro & Elim for objects/records
//| Object(record: map<string, Comp>)
//| Select(object: Comp, field: string)
// Elim for terminal computations as values
| Force(ref: Val)
// Elims for refs
//| Read(ref: Val)
//| Write(lhs: Val, rhs: Val)
{
    // TODO calculate Heap of a comp
}

// 
datatype Frame =
  Bind(var_: string, rhs: Comp)
| Call(arg: Val)
//| Select(field: string)

datatype Stack = Empty | Push(top: Frame, rest: Stack) {
    function Pop(): Option<(Frame, Stack)> {
        match this
        case Empty      => None
        case Push(t, r) => Some((t, r))
    }
}

// G |- (e, v) : A iff exists D. G |- e : D and D |- V : A
datatype Closure =
  Bool(bool)
| Int(int)
| Lambda(Env, string, Comp)
// G |- e : D iff for all x : A in D, G |- e[x] : A
type Env = map<string, Closure>

// CEK Machine
// In state = Computation, Environment, stacK
// (E, C, K) : B-   iff   E |- G  and  G |- C : A-  and  G |- K : A- << B-
type     In  = (Env, Comp, Stack)
// TODO calculate Heap of In
datatype Out = Next(In) | Stuck | Terminal

// G |- e : D and D |- v : A implies exists clo s.t. G |- clo : A
function Eval(env: Env, val: Val): Closure {
    match val
    case Var(x) =>
        assume {:axiom} x in env;
        env[x]
    case Bool(b)      => Closure.Bool(b)
    case Int(i)       => Closure.Int(i)
    case Lambda(b, f) => Closure.Lambda(env, b, f)
}

// This function either steps the current state or tells you that it's terminal/stuck
// Type soundness = well-typed configs don't get stuck!
// TODO: replace * with Heap of state
// TODO: shouldn't stuck be auto-propagated?
function Step(state: In): Out reads * {
    var (env, comp, stack) := state;
    match comp
    case Bind(lhs, var_, rhs) =>
        Next((env, lhs, Push(Frame.Bind(var_, rhs), stack)))
    
    case Pure(val) => (
        match stack.Pop()
        case Some((Bind(var_, rhs), stack)) =>
            Next((env[var_ := Eval(env, val)], rhs, stack))
        
        case Some(_) => Stuck
        // Lindley says you have to eval the val if it's a var
        case None    => Terminal
    )

    case Call(func, arg) =>
        Next((env, func, Push(Frame.Call(arg), stack)))
    
    case Func(bound, body) => (
        match stack.Pop()
        case Some((Call(arg), stack)) =>
            Next((env[bound := Eval(env, arg)], body, stack))
        
        case Some(_) => Stuck
        case None    => Terminal
    )

    case Ite(guard, then_, else_) => (
        match Eval(env, guard)
        case Bool(guard) =>
            Next((env, if guard then then_ else else_, stack))
        
        case _ => Stuck
    )

    // TODO: shadow the existing env like Lindley is not working
    // Converts lambdas/tuples to functions and records
    case Force(ref) =>
        match Eval(env, ref)
        case Lambda(env, b, f) => Next((env, Func(b, f), stack))
        
        case _        => Stuck
}

// Iterates step
method Run(s: In) decreases * {
    print("\n");
    match Step(s)
    case Next(s) => print(s, "\n"); Run(s);
    case _ => print "done/stuck\n"; return;
}

// Initial configuration
function Initial(comp: Comp): In
    { (map[], comp, Empty) }

method Main() decreases * {
    /*Run(Initial(
        Comp.Bind(
            Pure(Bool(true)),
            "x",
            Ite(
                Var("x"),
                Pure(Bool(false)),
                Pure(Bool(true))
            )
        )
    ));*/
    /*Run(Initial(
        Comp.Call(
            Comp.Call(
                Comp.Func(
                    "x",
                    Comp.Func(
                        "y",
                        Pure(Var("x"))
                    )
                ),
                Bool(true)
            ),
            Bool(false)
        )
    ));*/
    // Verifies that lexical scope works
    //var ptr := new Ptr(Func("y", Pure(Var("x"))));
    var fv := Val.Lambda("y", Pure(Var("x")));
    var fc := Force(Var("f"));
    var x1 := Val.Int(1);
    var x2 := Val.Int(2);
    var z  := Val.Int(0);
    Run(Initial(
        Comp.Call(
        Comp.Call(
        Comp.Call(
        Func("x",
        Func("f",
        Func("x",
            Comp.Call(fc, z)))),
        x2),
        fv),
        x1)
    ));
}