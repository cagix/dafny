include "../Dafny/AST.dfy"
  // Dafny to Rust compilation tenets:
  // - The Compiled Dafny AST should be minimal
  // - The generated code should look idiomatic and close to the original Dafny file if possible

// Rust AST
module RAST
  // All ToString methods should produce well-formed Rust code
{
  import opened Std.Wrappers
  import opened DAST.Format
  import Strings = Std.Strings

  // Default Indentation
  const IND := "  "

  datatype Mod =
      // Rust modules
    | Mod(name: string, body: seq<ModDecl>)
    | ExternMod(name: string)
  {
    function ToString(ind: string): string
      decreases this
    {
      match this {
        case ExternMod(name) =>
          "mod " + name + ";"
        case Mod(name, body) =>
          "mod " + name + " {" + "\n" + ind + IND +
          SeqToString(
            body,
            (modDecl: ModDecl) requires modDecl < this =>
              modDecl.ToString(ind + IND), "\n" + ind + IND)
          + "\n" + ind + "}"
      }
    }
  }
  function SeqToString<T>(s: seq<T>, f: T --> string, separator: string := ""): string
    requires forall t <- s :: f.requires(t)
  {
    if |s| == 0 then "" else
    f(s[0]) + (if |s| > 1 then separator + SeqToString(s[1..], f, separator) else "")
  }
  datatype ModDecl =
    | RawDecl(body: string)
    | ModDecl(mod: Mod)
    | StructDecl(struct: Struct)
    | EnumDecl(enum: Enum)
    | ImplDecl(impl: Impl)
    | TraitDecl(tr: Trait)
  {
    function ToString(ind: string): string
      decreases this
    {
      if ModDecl? then mod.ToString(ind)
      else if StructDecl? then struct.ToString(ind)
      else if ImplDecl? then impl.ToString(ind)
      else if EnumDecl? then enum.ToString(ind)
      else if TraitDecl? then tr.ToString(ind)
      else assert RawDecl?; body
    }
  }
  datatype Attribute = RawAttribute(content: string) {
    static function ToStringMultiple(attributes: seq<Attribute>, ind: string): string {
      SeqToString(
        attributes,
        (attribute: Attribute) => attribute.content + "\n" + ind)
    }
  }

  datatype Struct =
    Struct(attributes: seq<Attribute>,
           name: string, typeParams: seq<TypeParam>, fields: Fields)
  {
    function ToString(ind: string): string {
      Attribute.ToStringMultiple(attributes, ind) +
      "pub struct " + name +
      TypeParam.ToStringMultiple(typeParams, ind) +
      fields.ToString(ind, fields.NamedFields?) +
      (if fields.NamelessFields? then ";" else "")
    }
  }

  datatype NamelessField =
    NamelessField(visibility: Visibility, tpe: Type)
  {
    function ToString(ind: string): string {
      (if visibility == PUB then "pub " else "") + tpe.ToString(ind)
    }
  }

  datatype Field = Field(visibility: Visibility, formal: Formal)
  {
    function ToString(ind: string): string {
      (if visibility == PUB then "pub " else "") + formal.ToString(ind)
    }
  }

  datatype Fields =
    | NamedFields(fields: seq<Field>)
    | NamelessFields(types: seq<NamelessField>)
  {
    function ToString(ind: string, newLine: bool): string {
      if NamedFields? then
        var separator := if newLine then ",\n" + ind + IND else ", ";
        var (beginSpace, endSpace) :=
          if newLine && |fields| > 0 then
            ("\n" + ind + IND, "\n" + ind)
          else if |fields| > 0 then
            (" ", " ")
          else
            ("", "");
        " {" + beginSpace +
        SeqToString(fields, (field: Field) => field.ToString(ind + IND), separator)
        + endSpace + "}"
      else
        assert NamelessFields?;
        var separator := if newLine then ",\n" + ind + IND else ", ";
        "("+
        SeqToString(types, (t: NamelessField) => t.ToString(ind + IND), separator)
        +")"
    }
  }

  datatype EnumCase =
    | EnumCase(name: string, fields: Fields)
  {
    function ToString(ind: string, newLine: bool): string {
      name + fields.ToString(ind, newLine)
    }
  }

  datatype Enum =
    Enum(attributes: seq<Attribute>,
         name: string, typeParams: seq<TypeParam>,
         variants: seq<EnumCase>)
  {
    function ToString(ind: string): string {
      Attribute.ToStringMultiple(attributes, ind) +
      "pub enum " + name +
      TypeParam.ToStringMultiple(typeParams, ind)
      + " {" +
      SeqToString(
        variants,
        (variant: EnumCase) =>
          "\n" + ind + IND + variant.ToString(ind + IND, false), ",") +
      "\n" + ind + "}"
    }
  }

  type TypeParamConstraint = Type

  datatype TypeParam =
    | RawTypeParam(content: string, constraints: seq<TypeParamConstraint>)
  {
    static function ToStringMultiple(typeParams: seq<TypeParam>, ind: string): string {
      if |typeParams| == 0 then "" else
      "<" + SeqToString(typeParams, (t: TypeParam) => t.ToString(ind + IND), ", ") + ">"
    }
    static function {:tailrecursion true} AddConstraintsMultiple(
      typeParams: seq<TypeParam>, constraints: seq<TypeParamConstraint>
    ): seq<TypeParam> {
      if |typeParams| == 0 then []
      else
        [typeParams[0].AddConstraints(constraints)] + AddConstraintsMultiple(typeParams[1..], constraints)
    }
    function AddConstraints(constraints: seq<TypeParamConstraint>): TypeParam {
      this.(constraints := this.constraints + constraints)
    }
    function ToString(ind: string): string {
      content + (
        if |constraints| == 0 then
          ""
        else
          ": " + SeqToString(constraints, (t: TypeParamConstraint) requires t < this =>
                               t.ToString(ind + IND), " + "))
    }
  }
  const SelfBorrowed := Borrowed(SelfOwned)

  const SelfBorrowedMut := BorrowedMut(SelfOwned)

  const SelfPointer := Pointer(SelfOwned)

  const SelfPointerMut := PointerMut(SelfOwned)

  function Rc(underlying: Type): Type {
    TypeApp(std_type.MSel("rc").MSel("Rc"), [underlying])
  }
  function RefCell(underlying: Type): Type {
    TypeApp(std_type.MSel("cell").MSel("RefCell"), [underlying])
  }
  function Vec(underlying: Type): Type {
    TypeApp(std_type.MSel("vec").MSel("Vec"), [underlying])
  }
  function NewVec(elements: seq<Expr>): Expr {
    Identifier("vec!").Apply(elements)
  }
  function Clone(underlying: Expr): Expr {
    Select(underlying, "clone").Apply([])
  }
  function Borrow(underlying: Expr): Expr {
    UnaryOp("&", underlying, UnOpFormat.NoFormat)
  }
  function BorrowMut(underlying: Expr): Expr {
    UnaryOp("&mut", underlying, UnOpFormat.NoFormat)
  }

  const CloneTrait := RawType("Clone")
  const DafnyPrintTrait := RawType("::dafny_runtime::DafnyPrint")
  const DefaultTrait := RawType("::std::default::Default")
  const StaticTrait := RawType("'static")

  function RawType(content: string): Type {
    TIdentifier(content)
  }

  datatype Type =
    | SelfOwned
    | U8 | U16 | U32 | U64 | U128 | I8 | I16 | I32 | I64 | I128
    | Bool
    | TIdentifier(name: string)
    | TMemberSelect(base: Type, name: string)
    | TypeApp(baseName: Type, arguments: seq<Type>)
    | Borrowed(underlying: Type)
    | BorrowedMut(underlying: Type)
    | Pointer(underlying: Type)
    | PointerMut(underlying: Type)
    | ImplType(underlying: Type)
    | DynType(underlying: Type)
    | TupleType(arguments: seq<Type>)
    | FnType(arguments: seq<Type>, returnType: Type)
    | IntersectionType(left: Type, right: Type)
  {
    predicate HasCopySemantics() {
      U8? || U16? || U32? || U64? || U128? || I8? || I16? || I32? || I64? || I128? || Bool?
      || Pointer? || PointerMut?
    }
    predicate IsSelfPointer() {
      || (Borrowed? && underlying.PointerMut? && underlying.underlying.SelfOwned?)
      || (PointerMut? && underlying.SelfOwned?)
      || (PointerMut? && underlying.TypeApp? && |underlying.arguments| == 0 && underlying.baseName.SelfOwned?)
    }
    function ExtractMaybePlacebo(): Option<Type> {
      match this {
        case TypeApp(wrapper, arguments) =>
          if (wrapper == TIdentifier("MaybePlacebo")
              || wrapper == dafny_runtime_type.MSel("MaybePlacebo"))
              && |arguments| == 1
          then
            Some(arguments[0])
          else
            None
        case _ => None
      }
    }
    function ToString(ind: string): string {
      match this {
        case Bool() => "bool"
        case TIdentifier(underlying) => underlying
        case TMemberSelect(underlying, name) => underlying.ToString(ind) + "::" + name
        case Borrowed(underlying) => "&" + underlying.ToString(ind)
        case BorrowedMut(underlying) => "&mut " + underlying.ToString(ind)
        case Pointer(underlying) => "*const " + underlying.ToString(ind)
        case PointerMut(underlying) => "*mut " + underlying.ToString(ind)
        case ImplType(underlying) => "impl " + underlying.ToString(ind)
        case DynType(underlying) => "dyn " + underlying.ToString(ind)
        case FnType(arguments, returnType) =>
          "::std::ops::Fn("+
          SeqToString(arguments, (arg: Type) requires arg < this =>
                        arg.ToString(ind + IND), ", ")
          +") -> " + returnType.ToString(ind + IND)
        case IntersectionType(left, right) =>
          left.ToString(ind) + " + " + right.ToString(ind)
        case TupleType(args) =>
          (if args == [] then
             "()"
           else
             "(" +
             SeqToString(args, (arg: Type) requires arg < this => arg.ToString(ind + IND), ", ")
             + ")")
        case TypeApp(base, args) =>
          base.ToString(ind) +
          (if args == [] then
             ""
           else
             "<" +
             SeqToString(args, (arg: Type) requires arg < this => arg.ToString(ind + IND), ", ")
             + ">")

        case SelfOwned() => "Self"
        case U8() => "u8"
        case U16() => "u16"
        case U32() => "u32"
        case U64() => "u64"
        case U128() => "u128"
        case I8() => "i8"
        case I16() => "i16"
        case I32() => "i32"
        case I64() => "i64"
        case I128() => "i128"
      }
    }

    function MSel(name: string): Type {
      TMemberSelect(this, name)
    }

    function Apply1(arg: Type): Type {
      TypeApp(this, [arg])
    }

    function Apply(args: seq<Type>): Type {
      TypeApp(this, args)
    }
  }

  const global_type := TIdentifier("")
  const std_type := global_type.MSel("std")
  const super_type := TIdentifier("super")
  const cell_type := std_type.MSel("cell")
  const refcell_type := cell_type.MSel("RefCell")
  const dafny_runtime_type := global_type.MSel("dafny_runtime")

  function MaybePlaceboType(underlying: Type): Type {
    dafny_runtime_type.MSel("MaybePlacebo").Apply1(underlying)
  }


  datatype Trait =
    | Trait(typeParams: seq<TypeParam>, tpe: Type, where: string, body: seq<ImplMember>)
  {
    function ToString(ind: string): string {
      "pub trait " + TypeParam.ToStringMultiple(typeParams, ind) + tpe.ToString(ind)
      + (if where != "" then "\n" + ind + IND + where else "")
      + " {" +
      SeqToString(body, (member: ImplMember) => "\n" + ind + IND + member.ToString(ind + IND), "")
      + (if |body| == 0 then "" else "\n" + ind) + "}"
    }
  }

  datatype Impl =
    | ImplFor(typeParams: seq<TypeParam>, tpe: Type, forType: Type, where: string, body: seq<ImplMember>)
    | Impl(typeParams: seq<TypeParam>, tpe: Type, where: string, body: seq<ImplMember>)
  {
    function ToString(ind: string): string {
      "impl " + TypeParam.ToStringMultiple(typeParams, ind) + tpe.ToString(ind)
      + (if ImplFor? then " for " + forType.ToString(ind + IND) else "")
      + (if where != "" then "\n" + ind + IND + where else "")
      + " {" +
      SeqToString(body, (member: ImplMember) => "\n" + ind + IND + member.ToString(ind + IND), "")
      + (if |body| == 0 then "" else "\n" + ind) + "}"
    }
  }
  datatype ImplMember =
    | RawImplMember(content: string)
    | FnDecl(pub: Visibility, fun: Fn)
  {
    function ToString(ind: string): string {
      if FnDecl? then
        (if pub == PUB then "pub " else "") + fun.ToString(ind)
      else assert RawImplMember?; content
    }
  }
  datatype Visibility = PUB | PRIV

  datatype Formal =
    Formal(name: string, tpe: Type)
  {
    function ToString(ind: string): string {
      if name == "self" && tpe == SelfOwned then name
      else if name == "self" && tpe == SelfBorrowed then "&" + name
      else if name == "self" && tpe == SelfBorrowedMut then "&mut " + name
      else
        name + ": " + tpe.ToString(ind)
    }
    static const selfBorrowed := Formal("self", SelfBorrowed)
    static const selfOwned := Formal("self", SelfOwned)
    static const selfBorrowedMut := Formal("self", SelfBorrowedMut)
  }

  datatype Pattern =
    RawPattern(content: string)
  {
    function ToString(ind: string): string {
      content
    }
  }

  datatype MatchCase =
    MatchCase(pattern: Pattern, rhs: Expr)
  {
    function Height(): nat {
      1 + rhs.Height()
    }
    function ToString(ind: string): string
      decreases Height()
    {
      var newIndent := if rhs.Block? then ind else ind + IND;
      var rhsString := rhs.ToString(newIndent);

      pattern.ToString(ind) + " =>" +
      if '\n' in rhsString && rhsString[0] != '{' then "\n" + ind + IND + rhsString
      else " " + rhsString
    }
  }

  datatype AssignIdentifier =
    AssignIdentifier(identifier: string, rhs: Expr)
  {
    function Height(): nat {
      1 + rhs.Height()
    }

    function ToString(ind: string): string
      decreases Height()
    {
      identifier + ": " + rhs.ToString(ind + IND)
    }
  }

  // When a raw stream is given, try to put some indentation on it
  function AddIndent(raw: string, ind: string): string {
    if |raw| == 0 then raw
    else if raw[0] in "[({" then
      [raw[0]] + AddIndent(raw[1..], ind + IND)
    else if raw[0] in "})]" && |ind| > 2 then
      [raw[0]] + AddIndent(raw[1..], ind[..|ind|-2])
    else if raw[0] == '\n' then
      [raw[0]] + ind + AddIndent(raw[1..], ind)
    else
      [raw[0]] + AddIndent(raw[1..], ind)
  }

  function max(i: nat, j: nat): nat {
    if i < j then j else i
  }

  datatype DeclareType = MUT | CONST

  datatype Associativity = LeftToRight | RightToLeft | RequiresParentheses
  datatype PrintingInfo =
    | UnknownPrecedence()
    | Precedence(precedence: nat)
    | SuffixPrecedence(precedence: nat)
    | PrecedenceAssociativity(precedence: nat, associativity: Associativity)
  {
    predicate NeedParenthesesFor(underlying: PrintingInfo) {
      if UnknownPrecedence? then true
      else if underlying.UnknownPrecedence? then true
      else if precedence <= underlying.precedence then true
      else false
    }
    predicate NeedParenthesesForLeft(underlying: PrintingInfo) {
      if UnknownPrecedence? then true
      else if underlying.UnknownPrecedence? then true
      else if precedence <= underlying.precedence then
        precedence < underlying.precedence || !PrecedenceAssociativity? || !associativity.LeftToRight?
      else false
    }
    predicate NeedParenthesesForRight(underlying: PrintingInfo) {
      if UnknownPrecedence? then true
      else if underlying.UnknownPrecedence? then true
      else if precedence <= underlying.precedence then
        precedence < underlying.precedence || !PrecedenceAssociativity? || !associativity.RightToLeft?
      else false
    }
    lemma Tests()
      ensures PrecedenceAssociativity(20, LeftToRight)
              .NeedParenthesesForLeft(PrecedenceAssociativity(20, LeftToRight)) == false
      ensures PrecedenceAssociativity(20, LeftToRight)
              .NeedParenthesesForRight(PrecedenceAssociativity(20, LeftToRight)) == true
      ensures PrecedenceAssociativity(20, RightToLeft)
              .NeedParenthesesForRight(PrecedenceAssociativity(20, RightToLeft)) == false
      ensures PrecedenceAssociativity(20, RightToLeft)
              .NeedParenthesesForLeft(PrecedenceAssociativity(20, RightToLeft)) == true
      ensures PrecedenceAssociativity(20, LeftToRight)
              .NeedParenthesesForLeft(PrecedenceAssociativity(30, LeftToRight)) == true
      ensures PrecedenceAssociativity(20, RightToLeft)
              .NeedParenthesesForRight(PrecedenceAssociativity(30, RightToLeft)) == true
    {
    }
  }

  function AssignVar(name: string, rhs: Expr): Expr {
    Expr.Assign(Some(LocalVar(name)), rhs)
  }

  function AssignMember(on: Expr, field: string, rhs: Expr): Expr {
    Expr.Assign(Some(SelectMember(on, field)), rhs)
  }

  datatype AssignLhs =
    LocalVar(name: string) |
    SelectMember(on: Expr, field: string) |
    ExtractTuple(names: seq<string>)
    //| SelectIndex(expr: Expression, indices: seq<Expression>)

  datatype Expr =
      RawExpr(content: string)
    | ExprFromType(tpe: Type)
    | Identifier(name: string) // Can be empty for global in MemberSelect
    | Match(matchee: Expr, cases: seq<MatchCase>)
    | StmtExpr(stmt: Expr, rhs: Expr)
    | Block(underlying: Expr)
    | StructBuild(underlying: Expr, assignments: seq<AssignIdentifier>)
    | Tuple(arguments: seq<Expr>)
    | UnaryOp(op1: string, underlying: Expr, format: Format.UnOpFormat)
    | BinaryOp(op2: string, left: Expr, right: Expr, format2: Format.BinOpFormat)
    | TypeAscription(left: Expr, tpe: Type)          // underlying as tpe
    | LiteralInt(value: string)
    | LiteralBool(bvalue: bool)
    | LiteralString(value: string, binary: bool)
    | DeclareVar(declareType: DeclareType, name: string, optType: Option<Type>, optRhs: Option<Expr>) // let mut name: optType = optRhs;
    | Assign(names: Option<AssignLhs>, rhs: Expr)           // name1, name2 = rhs;
    | IfExpr(cond: Expr, thn: Expr, els: Expr)       // if cond { thn } else { els }
    | Loop(optCond: Option<Expr>, underlying: Expr)  // loop { body }
    | For(name: string, range: Expr, body: Expr)     // for name in range { body }
    | Labelled(lbl: string, underlying: Expr)        // label lbl { expr }
    | Break(optLbl: Option<string>)                  // break lbl;
    | Continue(optLbl: Option<string>)               // continue optLabel;
    | Return(optExpr: Option<Expr>)                  // return optExpr;
    | CallType(obj: Expr, typeParameters: seq<Type>) // obj::<...type parameters>
    | Call(obj: Expr, arguments: seq<Expr>)          // obj(...arguments)
    | Select(obj: Expr, name: string)                // obj.name
    | MemberSelect(obj: Expr, name: string)          // obj::name
  {
    predicate NoExtraSemicolonAfter() {
      DeclareVar? || Assign? || Break? || Continue? || Return? ||
      (RawExpr? && |content| > 0 && content[|content| - 1] == ';')
    }
    // Taken from https://doc.rust-lang.org/reference/expressions.html
    const printingInfo: PrintingInfo :=
      match this {
        case RawExpr(_) => UnknownPrecedence()
        case ExprFromType(_) => Precedence(1)
        case Identifier(_) => Precedence(1)
        case LiteralInt(_) => Precedence(1)
        case LiteralBool(_) => Precedence(1)
        case LiteralString(_, _) => Precedence(1)
        // Paths => Precedence(1)
        // Method call => Precedence(2)
        // Field expression => PrecedenceAssociativity(3, LeftToRight)
        // case function call | ArrayIndexing => Precedence(4)
        case UnaryOp(op, underlying, format) =>
          match op {
            case "?" => SuffixPrecedence(5)
            case "-" | "*" | "!" | "&" | "&mut" => Precedence(6)
            case _ => UnknownPrecedence()
          }
        case Select(underlying, name) => PrecedenceAssociativity(2, LeftToRight)
        case MemberSelect(underlying, name) => PrecedenceAssociativity(2, LeftToRight)
        case CallType(_, _) => PrecedenceAssociativity(2, LeftToRight)
        case Call(_, _) => PrecedenceAssociativity(2, LeftToRight)
        case TypeAscription(left, tpe) =>
          PrecedenceAssociativity(10, LeftToRight)
        case BinaryOp(op2, left, right, format) =>
          match op2 {
            case "*" | "/" | "%" => PrecedenceAssociativity(20, LeftToRight)
            case "+" | "-" => PrecedenceAssociativity(30, LeftToRight)
            case "<<" | ">>" => PrecedenceAssociativity(40, LeftToRight)
            case "&" => PrecedenceAssociativity(50, LeftToRight)
            case "^" => PrecedenceAssociativity(60, LeftToRight)
            case "|" => PrecedenceAssociativity(70, LeftToRight)
            case "==" | "!=" | "<" | ">" | "<=" | ">=" => PrecedenceAssociativity(80, RequiresParentheses)
            case "&&" => PrecedenceAssociativity(90, LeftToRight)
            case "||" => PrecedenceAssociativity(100, LeftToRight)
            case ".." | "..=" => PrecedenceAssociativity(110, RequiresParentheses)
            case "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=" =>
              PrecedenceAssociativity(110, RightToLeft)
            case _ => PrecedenceAssociativity(0, RequiresParentheses)
          }
        case _ => UnknownPrecedence()
      }

    function Height(): nat {
      match this {
        case Identifier(_) => 1
        case ExprFromType(_) => 1
        case LiteralInt(_) => 1
        case LiteralBool(_) => 1
        case LiteralString(_, _) => 1
        case Match(matchee, cases) =>
          1 + max(matchee.Height(),
                  SeqToHeight(cases, (oneCase: MatchCase)
                              requires oneCase < this
                              => oneCase.Height()))
        case StmtExpr(stmt, rhs) =>
          var default := 1 + max(stmt.Height(), rhs.Height());
          match this {
            case StmtExpr(DeclareVar(mod, name, Some(tpe), None), StmtExpr(Assign(name2, rhs), last)) =>
              if name2 == Some(LocalVar(name)) then
                1 + default
              else default
            case StmtExpr(IfExpr(UnaryOp("!", BinaryOp("==", a, b, f), of), RawExpr("panic!(\"Halt\");"), RawExpr("")), last) =>
              1 + default
            case _ => default
          }

        case Block(underlying) =>
          1 + underlying.Height()
        case StructBuild(name, assignments) =>
          1 + max(name.Height(), SeqToHeight(assignments, (assignment: AssignIdentifier)
                          requires assignment < this
                          => assignment.Height()))
        case Tuple(arguments) =>
          1 + SeqToHeight(arguments, (argument: Expr)
                          requires argument < this
                          => argument.Height())
        // Special cases
        case UnaryOp(_, underlying, _) => 1 + underlying.Height()
        case TypeAscription(left, tpe) => 1 + left.Height()
        case BinaryOp(op, left, right, format) =>
          1 + max(left.Height(), right.Height())
        case IfExpr(cond, thn, els) =>
          1 + max(cond.Height(), max(thn.Height(), els.Height()))
        case DeclareVar(declareType, name, tpe, expr) =>
          1 + (match expr {
                 case Some(e) => e.Height()
                 case None => 0
               })
        case Assign(names, expr) =>
          match names {
            case Some(SelectMember(on, field)) => 1+max(on.Height(), expr.Height())
            case _ => 1 + expr.Height()
          }
        case Loop(optCond, underlying) =>
          1 + if optCond.Some? then max(optCond.value.Height(), underlying.Height()) else underlying.Height()
        case Labelled(lbl, underlying) =>
          1 + underlying.Height()
        case Break(_) => 1
        case Continue(_) => 1
        case For(name, range, body) =>
          1 + max(range.Height(), body.Height())
        case Return(optExpr) =>
          if optExpr.Some? then 1 + optExpr.value.Height() else 1
        case CallType(obj, tpes) =>
          1 + max(obj.Height(),
                  SeqToHeight(tpes, (tpe: Type) requires tpe < this => 1))
        case Call(obj, args) =>
          1 + max(obj.Height(),
                  SeqToHeight(args, (arg: Expr) requires arg < this => arg.Height()))
        case Select(expression, name) =>
          1 + expression.Height()
        case MemberSelect(expression, name) =>
          1 + expression.Height()
        case _ =>
          assert RawExpr?;
          1
      }
    }

    // Wish: Prove that Optimize() preserves semantics, if any
    // TODO: Ensure that even without Optimize(), tests pass
    opaque function Optimize(): (r: Expr)
      ensures this == r || r.Height() < this.Height()
    {
      match this {
        case UnaryOp("&", Call(Select(underlying, "clone"), args), format) =>
          if args == [] then
            assert Select(underlying, "clone").Height() == 1 + underlying.Height();
            assert Call(Select(underlying, "clone"), args).Height() == 2 + underlying.Height();
            assert UnaryOp("&", underlying, format).Height() == 1 + underlying.Height();
            UnaryOp("&", underlying, format)
          else
            this

        case UnaryOp("!", BinaryOp("==", left, right, format),
          CombineNotInner()) =>
          assert BinaryOp("==", left, right, format).Height()
              == BinaryOp("!=", left, right, BinOpFormat.NoFormat()).Height();
          BinaryOp("!=", left, right, BinOpFormat.NoFormat())

        case UnaryOp("!", BinaryOp("<", left, right, NoFormat()),
          CombineNotInner()) =>
          assert BinaryOp(">=", left, right, BinOpFormat.NoFormat()).Height()
              == BinaryOp("<", left, right, BinOpFormat.NoFormat()).Height();
          BinaryOp(">=", left, right, BinOpFormat.NoFormat())

        case UnaryOp("!", BinaryOp("<", left, right, ReverseOperands()),
          CombineNotInner()) =>
          assert BinaryOp("<=", right, left, BinOpFormat.NoFormat()).Height()
              == BinaryOp("<", left, right, BinOpFormat.ReverseOperands()).Height();
          BinaryOp("<=", right, left, BinOpFormat.NoFormat())
        case Call(MemberSelect(r, "truncate!"), args) =>
          if (r != dafny_runtime && r != global) || |args| != 2  then
            this
          else
            var expr := args[0];
            var tpeExpr := args[1];
            if !tpeExpr.ExprFromType? then this else
            var tpe := tpeExpr.tpe;
            if || tpe.U8? || tpe.U16? || tpe.U32? || tpe.U64? || tpe.U128?
               || tpe.I8? || tpe.I16? || tpe.I32? || tpe.I64? || tpe.I128? then
            match expr {
              case Call(
                MemberSelect(base, "int!"), args) =>
                if |args| == 1 && (base == dafny_runtime || base == global) then
                  match args[0] {
                    case LiteralInt(number) => LiteralInt(number)
                    case LiteralString(number, _) => LiteralInt(number)
                    case _ => this
                  }
                else this
              case _ => this
            }
          else
            this
        case StmtExpr(DeclareVar(mod, name, Some(tpe), None), StmtExpr(Assign(name2, rhs), last)) =>
          if name2 == Some(LocalVar(name)) then
            var rewriting := StmtExpr(DeclareVar(mod, name, Some(tpe), Some(rhs)), last);
            assert rewriting.Height() < this.Height() by {
              assert StmtExpr(Assign(name2, rhs), last).Height() ==
                     1 + max(Assign(name2, rhs).Height(), last.Height()) ==
                     1 + max(1 + rhs.Height(), last.Height());
              assert this.Height() == 2 + max(1, 1 + max(1 + rhs.Height(), last.Height()));
              assert rewriting.Height() == 1 + max(1 + rhs.Height(), last.Height());
            }
            rewriting
          else
            this
        case StmtExpr(IfExpr(UnaryOp("!", BinaryOp("==", a, b, f), of), RawExpr("panic!(\"Halt\");"), RawExpr("")), last) =>
          var rewriting := StmtExpr(Identifier("assert_eq!").Apply([a, b]), last);
          assume {:axiom} rewriting.Height() < this.Height(); // TODO: Need to prove formally
          rewriting
        case _ => this
      }
    }

    predicate LeftRequiresParentheses(left: Expr) {
      printingInfo.NeedParenthesesForLeft(left.printingInfo)
    }
    function LeftParentheses(left: Expr): (string, string) {
      if LeftRequiresParentheses(left) then
        ("(", ")")
      else
        ("", "")
    }

    predicate RightRequiresParentheses(right: Expr) {
      printingInfo.NeedParenthesesForRight(right.printingInfo)
    }


    function RightParentheses(right: Expr): (string, string) {
      if RightRequiresParentheses(right) then
        ("(", ")")
      else
        ("", "")
    }

    function RightMostIdentifier(): Option<string> {
      match this {
        case MemberSelect(_, id) => Some(id)
        case _ => None
      }
    }

    function ToString(ind: string): string
      decreases Height()
    {
      match this.Optimize() {
        case Identifier(name) => name
        case ExprFromType(t) => t.ToString(ind)
        case LiteralInt(number) => number
        case LiteralBool(b) => if b then "true" else "false"
        case LiteralString(characters, binary) =>
          (if binary then "b" else "") +
          "\"" + characters + "\""
        case Match(matchee, cases) =>
          "match " + matchee.ToString(ind + IND) + " {" +
          SeqToString(cases,
                      (c: MatchCase) requires c.Height() < this.Height() =>
                        "\n" + ind + IND + c.ToString(ind + IND), ",") +
          "\n" + ind + "}"
        case StmtExpr(stmt, rhs) => // They are built like StmtExpr(1, StmtExpr(2, StmtExpr(3, ...)))
          if stmt.RawExpr? && stmt.content == "" then rhs.ToString(ind) else
          stmt.ToString(ind) + (if stmt.NoExtraSemicolonAfter() then "" else ";") +
          "\n" + ind + rhs.ToString(ind)
        case Block(underlying) =>
          "{\n" + ind + IND + underlying.ToString(ind + IND) + "\n" + ind + "}"
        case IfExpr(cond, thn, els) =>
          "if " + cond.ToString(ind + IND) + " {\n" + ind + IND + thn.ToString(ind + IND) +
          "\n" + ind + "}" +
          if els == RawExpr("") then "" else
           " else {\n" + ind + IND + els.ToString(ind + IND) + "\n" + ind + "}"
        case StructBuild(name, assignments) =>
          name.ToString(ind) + " {" +
          SeqToString(assignments, (assignment: AssignIdentifier)
                      requires assignment.Height() < this.Height()
                      =>
                        "\n" + ind + IND + assignment.ToString(ind + IND), ",") +
          (if |assignments| > 0 then "\n" + ind else "") + "}"
        case Tuple(arguments) =>
          "(" +
          SeqToString(arguments, (arg: Expr)
                      requires arg.Height() < this.Height()
                      =>
                        "\n" + ind + IND + arg.ToString(ind + IND), ",") +
          (if |arguments| > 0 then "\n" + ind else "") + ")"

        case UnaryOp(op, underlying, format) =>
          var (leftP, rightP) :=
            if printingInfo.NeedParenthesesFor(underlying.printingInfo) then
              ("(", ")")
            else
              ("", "");
          var leftOp := if op == "&mut" && leftP != "(" then op + " " else if op == "?" then "" else op;
          var rightOp := if op == "?" then op else "";

          leftOp + leftP  + underlying.ToString(ind) + rightP + rightOp
        case TypeAscription(left, tpe) =>
          var (leftLeftP, leftRightP) := LeftParentheses(left);
          leftLeftP + left.ToString(IND) + leftRightP + " as " + tpe.ToString(IND)
        case BinaryOp(op2, left, right, format) =>
          var (leftLeftP, leftRighP) := LeftParentheses(left);
          var (rightLeftP, rightRightP) := RightParentheses(right);
          var opRendered := " " + op2 + " ";
          var indLeft := if leftLeftP == "(" then ind + IND else ind;
          var indRight := if rightLeftP == "(" then ind + IND else ind;
          leftLeftP + left.ToString(indLeft) + leftRighP + opRendered + rightLeftP + right.ToString(indRight) + rightRightP
        case DeclareVar(declareType, name, optType, optExpr) =>
          "let " + (if declareType == MUT then "mut " else "") +
          name + (if optType.Some? then ": " + optType.value.ToString(ind + IND) else "") +

          (if optExpr.Some? then
             var optExprString := optExpr.value.ToString(ind + IND);
             if optExprString == "" then
               "= /*issue with empty RHS*/" + match optExpr.value {
                 case RawExpr(_) => "Empty Raw expr"
                 case LiteralString(_, _) => "Empty string literal"
                 case LiteralInt(_) => "Empty int literal"
                 case _ => "Another case"
               }
             else " = " + optExprString else "") + ";"
        case Assign(names, expr) =>
          var lhs := match names {
            case Some(LocalVar(name)) => name + " = "
            case Some(SelectMember(member, field)) =>
              var (leftP, rightP) := Select(member, field).LeftParentheses(member);
              leftP + member.ToString(IND) + rightP + "." + field + " = "
            case Some(ExtractTuple(names)) => "(" + SeqToString(names, (name: string) => name, ",") + ") = "
            case None => "_ = "
          };
          lhs + expr.ToString(ind + IND) + ";"
        case Labelled(name, underlying) =>
          "'" + name + ": " + underlying.ToString(ind)
        case Break(optLbl) =>
          match optLbl {
            case Some(lbl) => "break '" + lbl + ";"
            case None => "break;"
          }
        case Continue(optLbl) =>
          match optLbl {
            case Some(lbl) => "continue '" + lbl + ";"
            case None => "continue;"
          }
        case Loop(optCond, underlying) =>
          (match optCond {
             case None => "loop"
             case Some(c) => "while " + c.ToString(ind + IND)
           }) + " {\n" + ind + IND + underlying.ToString(ind + IND) + "\n" + ind + "}"
        case For(name, range, body) =>
          "for "+ name +" in " + range.ToString(ind + IND) + " {\n" + ind + IND +
          body.ToString(ind + IND) + "\n" + ind + "}"
        case Return(optExpr) =>
          "return" + (if optExpr.Some? then " " + optExpr.value.ToString(ind + IND) else "") + ";"
        case CallType(expr, tpes) =>
          var (leftP, rightP) := LeftParentheses(expr);
          if tpes == [] then expr.ToString(ind) else
          leftP + expr.ToString(ind) + rightP + "::<" + 
            SeqToString(tpes, (tpe: Type) => tpe.ToString(ind + IND), ", ") +">"
          
        case Call(expr, args) =>
          var (leftP, rightP) := LeftParentheses(expr);
          var (leftCallP, rightCallP) := match expr.RightMostIdentifier() {
            case Some("seq!") | Some("map!")  =>
              ("[","]")
            case Some("set!") | Some("multiset!") =>
              ("{","}")
            case _ =>
              ("(", ")")
          };
          leftP + expr.ToString(ind) + rightP +
          leftCallP + SeqToString(args, (arg: Expr) requires arg.Height() < this.Height() => arg.ToString(ind + IND), ", ")+ rightCallP
        case Select(expression, name) =>
          var (leftP, rightP) := LeftParentheses(expression);
          leftP + expression.ToString(ind) + rightP + "." + name
        case MemberSelect(expression, name) =>
          var (leftP, rightP) := LeftParentheses(expression);
          leftP + expression.ToString(ind) + rightP + "::" + name
        case r =>
          assert r.RawExpr?; AddIndent(r.content, ind)
      }
    }
    function Then(rhs2: Expr): Expr {
      if this.StmtExpr? then
        StmtExpr(stmt, rhs.Then(rhs2))
      else if this == RawExpr("") then
        rhs2
      else
        StmtExpr(this, rhs2)
    }

    // Helpers

    function Sel(name: string): Expr {
      Select(this, name)
    }
    function MSel(name: string): Expr {
      MemberSelect(this, name)
    }
    function ApplyType(typeParameters: seq<Type>): Expr {
      CallType(this, typeParameters)
    }
    function ApplyType1(typeParameter: Type): Expr {
      CallType(this, [typeParameter])
    }
    function Apply(arguments: seq<Expr>): Expr {
      Call(this, arguments)
    }
    
    function Apply1(argument: Expr): Expr {
      Call(this, [argument])
    }
  }

  const self := Identifier("self")

  const global := Identifier("")

  const dafny_runtime := global.MSel("dafny_runtime")
  const dafny_runtime_Set := dafny_runtime.MSel("Set")
  const dafny_runtime_Set_from_array := dafny_runtime_Set.MSel("from_array")
  const dafny_runtime_Sequence := dafny_runtime.MSel("Sequence")
  const Sequence_from_array_owned := dafny_runtime_Sequence.MSel("from_array_owned")
  const Sequence_from_array := dafny_runtime_Sequence.MSel("from_array")
  const dafny_runtime_Multiset := dafny_runtime.MSel("Multiset")
  const dafny_runtime_Multiset_from_array := dafny_runtime_Multiset.MSel("from_array")
  function MaybePlacebo(underlying: Expr): Expr {
    dafny_runtime.MSel("MaybePlacebo").MSel("from").Apply1(underlying)
  }

  const std := global.MSel("std")

  const std_rc := std.MSel("rc")

  const std_rc_Rc := std_rc.MSel("Rc")

  const std_rc_Rc_new := std_rc_Rc.MSel("new")

  const std_Default_default := std.MSel("default").MSel("Default").MSel("default").Apply([])

  function RcNew(underlying: Expr): Expr {
    Call(std_rc_Rc_new, [underlying])
  }

  datatype Fn =
    Fn(name: string, typeParams: seq<TypeParam>, formals: seq<Formal>,
       returnType: Option<Type>,
       where: string,
       body: Option<Expr>)
  {
    function ToString(ind: string): string {
      "fn " + name + TypeParam.ToStringMultiple(typeParams, ind) +
      "(" + SeqToString(formals, (formal: Formal) => formal.ToString(ind), ", ") + ")" +
      (match returnType case Some(t) => " -> " + t.ToString(ind) case _ => "") +
      (if where == "" then "" else "\n" + ind + IND + where) +
      match body {
        case None => ";"
        case Some(body) =>
          " {\n" + ind + IND +
          body.ToString(ind + IND) +
          "\n" + ind + "}"
      }
    }
  }
}

abstract module {:extern "DafnyToRustCompilerAbstract"} DafnyToRustCompilerAbstract {
  import opened DAST
  import Strings = Std.Strings
  import Std
  import opened Std.Wrappers
  import R = RAST
  const IND := R.IND
  type Type = DAST.Type
  type Formal = DAST.Formal

  const UnicodeChars: bool

  // List taken from https://doc.rust-lang.org/book/appendix-01-keywords.html
  const reserved_rust := {
    "as","async","await","break","const","continue",
    "crate","dyn","else","enum","extern","false","fn","for","if","impl",
    "in","let","loop","match","mod","move","mut","pub","ref","return",
    "Self","self","static","struct","super","trait","true","type","union",
    "unsafe","use","where","while","Keywords","The","abstract","become",
    "box","do","final","macro","override","priv","try","typeof","unsized",
    "virtual","yield"}
  const reserved_rust_need_prefix := {"u8", "u16", "u32", "u64", "u128","i8", "i16", "i32", "i64", "i128"}

  predicate is_tuple_numeric(i: string) {
    |i| >= 2 && i[0] == '_' &&
    i[1] in "0123456789" &&
    (|i| == 2 ||
     (|i| == 3 && i[2] in "0123456789"))
  }

  predicate has_special(i: string) {
    if |i| == 0 then false
    else if i[0] == '.' then true
    else if i[0] == '#' then true // otherwise "escapeIdent("r#") becomes "r#""
    else if i[0] == '_' then
      if 2 <= |i| then
        if i[1] != '_' then true
        else has_special(i[2..])
      else
        true
    else
      has_special(i[1..])
  }

  function idiomatic_rust(i: string): string
    requires !has_special(i)
  {
    if |i| == 0 then ""
    else if i[0] == '_' then
      assert 2 <= |i| && i[1] == '_';
      "_" + idiomatic_rust(i[2..])
    else
      [i[0]] + idiomatic_rust(i[1..])
  }

  function replaceDots(i: string): string {
    if |i| == 0 then
      ""
    else if i[0] == '.' then
      "_d" + replaceDots(i[1..])
    else
      [i[0]] + replaceDots(i[1..])
  }

  predicate is_tuple_builder(i: string)
    // A tuple builder identifier looks like ___hMake0 to ___hMake99
  {
    && |i| >= 9
    && i[..8] == "___hMake"
    && i[8] in "0123456789"
    && (|i| == 9 || (|i| == 10 && i[9] in "0123456789"))
  }

  function better_tuple_builder_name(i: string): string
    requires is_tuple_builder(i)
  {
    "_T" + i[8..]
  }

  predicate is_dafny_generated_id(i: string) {
    && |i| > 0 && i[0] == '_' && !has_special(i[1..])
    && (|i| >= 2 ==> i[1] != 'T') // To avoid conflict with tuple builders _T<digits>
  }

  predicate is_idiomatic_rust_id(i: string) {
    0 < |i| && !has_special(i) && i !in reserved_rust && i !in reserved_rust_need_prefix
  }

  function escapeIdent(i: string): string {
    if is_tuple_numeric(i) then
      i
    else if is_tuple_builder(i) then
      better_tuple_builder_name(i)
    else if i in reserved_rust then
      "r#" + i
    else if is_idiomatic_rust_id(i) then
      idiomatic_rust(i)
    else if is_dafny_generated_id(i) then
      i // Dafny-generated identifiers like "_module", cannot be written in Dafny itself
    else
      var r := replaceDots(i);
      "r#_" + r
  }

  datatype Ownership = OwnershipOwned | OwnershipBorrowed | OwnershipBorrowedMut | OwnershipAutoBorrowed

  const DafnyChar := if UnicodeChars then "DafnyChar" else "DafnyCharUTF16"
  const DafnyCharUnderlying := if UnicodeChars then R.RawType("char") else R.RawType("u16")

  datatype UnassignedStatus = Unassigned | WithTracker(tracker_name: string)

  // types stores the Rust type per Rust name.
  // fn Test<T>(i: T) is map["i" := R.RawType("T")]
  // fn Test(i: &T) is map["i" := R.Borrowed(...)]
  // fn Test(i: &mut T) is map["i" := R.BorrowedMut(...)]
  
  datatype Environment = Environment(
    names: seq<string>,                 // All variable names, after escape, in Rust
    types: map<string, R.Type>
  ) {
    static function Empty(): Environment {
      Environment([], map[])
    }
    opaque predicate HasCopySemantics(name: string) {
      name in types && types[name].HasCopySemantics()
    }
    opaque predicate HasCloneSemantics(name: string) {
      !HasCopySemantics(name)
    }
    function GetType(name: string): Option<R.Type> {
      if name in types then Some(types[name]) else None
    }
    predicate IsBorrowed(name: string) {
      name in types && types[name].Borrowed?
    }
    predicate IsBorrowedMut(name: string) {
      name in types && types[name].BorrowedMut?
    }
    function AddAssigned(name: string, tpe: R.Type): Environment
      // If we know for sure the type of name extends the Copy trait
    {
      Environment(names + [name], types[name := tpe])
    }
    function RemoveAssigned(name: string): Environment
      requires name in names
    {
      var indexInEnv := Std.Collections.Seq.IndexOf(names, name);
      Environment(
        names[0..indexInEnv] + names[indexInEnv + 1..],
        types - {name}
      )
    }
  }

  const ASSIGNED_PREFIX := "_set"

  function AddAssignedPrefix(rustName: string): string {
    if |rustName| >= 2 && rustName[0..2] == "r#" then
      ASSIGNED_PREFIX + rustName[2..]
    else
      ASSIGNED_PREFIX + "_" + rustName
  }
  class COMP {
    static method GenModule(mod: Module, containingPath: seq<Ident>) returns (s: R.Mod) {
      var body := GenModuleBody(mod.body, containingPath + [Ident.Ident(mod.name)]);

      s := if mod.isExtern then
        R.ExternMod(escapeIdent(mod.name))
      else
        R.Mod(escapeIdent(mod.name), body);
    }

    static method GenModuleBody(body: seq<ModuleItem>, containingPath: seq<Ident>) returns (s: seq<R.ModDecl>) {
      s := [];
      if containingPath == [Ident.Ident("_System")] {
        s := s + [
          R.TraitDecl(R.Trait([], R.TIdentifier("object"), "", []))
        ];
      }
      for i := 0 to |body| {
        var generated;
        match body[i] {
          case Module(m) =>
            var mm := GenModule(m, containingPath);
            generated := [R.ModDecl(mm)];
          case Class(c) =>
            generated := GenClass(c, containingPath + [Ident.Ident(c.name)]);
          case Trait(t) =>
            var tt := GenTrait(t, containingPath);
            generated := [R.RawDecl(tt)];
          case Newtype(n) =>
            generated := GenNewtype(n);
          case Datatype(d) =>
            generated := GenDatatype(d);
        }
        s := s + generated;
      }
    }

    static method GenTypeParameters(params: seq<Type>)
      returns (
        typeParamsSet: set<Type>,
        typeParams: seq<R.TypeParam>,
        constrainedTypeParams: seq<R.TypeParam>,
        whereConstraints: string)
    {
      typeParamsSet := {};
      typeParams := [];
      constrainedTypeParams := [];
      whereConstraints := "";
      var tpI := 0;

      if |params| > 0 {
        while tpI < |params| {
          var tp := params[tpI];
          typeParamsSet := typeParamsSet + {tp};
          var genTp := GenType(tp, false, false);
          typeParams := typeParams + [R.RawTypeParam(genTp.ToString(IND), [])];
          tpI := tpI + 1;
        }
      }
      var baseConstraints := [R.CloneTrait, R.DafnyPrintTrait, R.StaticTrait];
      constrainedTypeParams := R.TypeParam.AddConstraintsMultiple(
        typeParams, baseConstraints
      );
    }

    static method GenClass(c: Class, path: seq<Ident>) returns (s: seq<R.ModDecl>) {
      var typeParamsSet, sTypeParams, sConstrainedTypeParams, whereConstraints := GenTypeParameters(c.typeParams);
      var constrainedTypeParams := R.TypeParam.ToStringMultiple(sConstrainedTypeParams, R.IND + R.IND);

      var fields: seq<R.Field> := [];
      var fieldInits: seq<R.AssignIdentifier> := [];
      var fieldI := 0;
      while fieldI < |c.fields| {
        var field := c.fields[fieldI];
        var fieldType := GenType(field.formal.typ, false, false);
        var fieldRustName := escapeIdent(field.formal.name);
        fields := fields + [R.Field(R.PUB, R.Formal(fieldRustName, fieldType))];

        match field.defaultValue {
          case Some(e) => {
            // TODO(mikael): Fields must be initialized before the code of the constructor if possible
            var expr, _, _ := GenExpr(e, None, Environment.Empty(), OwnershipOwned);

            fieldInits := fieldInits + [
              R.AssignIdentifier(
                fieldRustName, expr)];
          }
          case None => {
            // TODO(mikael) Use type descriptors for default values if generics
            var default := R.std_Default_default;
            if fieldType.PointerMut? {
              default := R.std.MSel("ptr").MSel("null_mut").Apply([]);
            } else if fieldType.Pointer? {
              default := R.std.MSel("ptr").MSel("null").Apply([]);
            }
            fieldInits := fieldInits + [
              R.AssignIdentifier(
                fieldRustName, default)];
          }
        }

        fieldI := fieldI + 1;
      }

      // A phantom field is necessary to avoid Rust complaining about no reference to the type parameter.
      // PhantomData is zero-sized so it won't impact final performance or layout
      for typeParamI := 0 to |c.typeParams| {
        var tpeGen := GenType(c.typeParams[typeParamI], false, false);
        fields := fields + [
          R.Field(R.PRIV,
            R.Formal("_phantom_type_param_" + Strings.OfNat(typeParamI),
            R.TypeApp(R.std_type.MSel("marker").MSel("PhantomData"), [tpeGen])))];
        fieldInits := fieldInits + [
          R.AssignIdentifier(
            "_phantom_type_param_" + Strings.OfNat(typeParamI),
            R.RawExpr("::std::marker::PhantomData"))];
      }

      var datatypeName := escapeIdent(c.name);

      var struct := R.Struct([], datatypeName, sTypeParams, R.NamedFields(fields));
      var typeParamsAsTypes :=
        Std.Collections.Seq.Map((typeParam: R.TypeParam) => R.RawType(typeParam.content), sTypeParams);

      s := [R.StructDecl(struct)];

      var underlyingDatatype := Type.Path([], [],
        ResolvedType.Datatype(DatatypeType(path, c.attributes)));
      /*var underlyingDatatypeRust := GenType(underlyingDatatype, false, false);
      underlyingDatatypeRust := underlyingDatatypeRust.Apply(Std.Collections.Seq.Map(
        (typeParam: R.TypeParam) => R.TIdentifier(typeParam.content),
        sTypeParams));*/

      var implBodyRaw, traitBodies := GenClassImplBody(c.body, false, Type.Path([], [],
        ResolvedType.AllocatedDatatype(DatatypeType(path, c.attributes))), typeParamsSet);
      var implBody :=
        [R.FnDecl(
          R.PUB,
          R.Fn("new", [], [], Some(R.SelfOwned), "",
               Some(
                    R.StructBuild(
                      R.Identifier(datatypeName),
                      fieldInits
                    ))
           ))] + [
              R.FnDecl(
                R.PUB,
                R.Fn("_allocated",
                  [], [], Some(R.SelfPointerMut),
                  "",
                  Some(
                    R.dafny_runtime.MSel("allocate").ApplyType1(R.SelfOwned).Apply([])
                  ))
              )
           ] + implBodyRaw;

      var i := R.Impl(
        sConstrainedTypeParams,
        R.TypeApp(R.TIdentifier(datatypeName), typeParamsAsTypes),
        whereConstraints,
        implBody
      );
      s := s + [R.ImplDecl(i)];
      if (|c.superClasses| > 0) {
        var i := 0;
        while i < |c.superClasses| {
          var superClass := c.superClasses[i];
          match superClass {
            case Path(traitPath, typeArgs, Trait(_, _)) => {
              var pathStr := GenPath(traitPath);
              var typeArgs := GenTypeArgs(typeArgs, false, false);
              var body: seq<R.ImplMember> := [];
              if traitPath in traitBodies {
                body := traitBodies[traitPath];
              }

              var genSelfPath := GenPath(path);
              var x := R.ImplDecl(
                R.ImplFor(
                  sConstrainedTypeParams,
                  R.TypeApp(pathStr, typeArgs),
                  R.Rc(R.TypeApp(genSelfPath, typeParamsAsTypes)),
                  whereConstraints,
                  body
                ));
              s := s + [x];
            }
            case _ => {}
          }
          i := i + 1;
        }
      }

      var d := R.ImplFor(
        sConstrainedTypeParams,
        R.DefaultTrait,
        R.TypeApp(R.TIdentifier(datatypeName), typeParamsAsTypes),
        whereConstraints,
        [R.FnDecl(
           R.PRIV,
           R.Fn(
             "default", [], [], Some(R.SelfOwned),
             "",
             Some(R.RawExpr(datatypeName + "::new()"))))]
      );
      var defaultImpl := [R.ImplDecl(d)];

      var p :=
        R.ImplFor(
          sConstrainedTypeParams,
          R.DafnyPrintTrait,
          R.TypeApp(R.TIdentifier(datatypeName), typeParamsAsTypes),
          "",
          [R.FnDecl(
             R.PRIV,
             R.Fn(
               "fmt_print", [],
               [R.Formal.selfBorrowed, R.Formal("_formatter", R.RawType("&mut ::std::fmt::Formatter")), R.Formal("_in_seq", R.Type.Bool)],
               Some(R.RawType("std::fmt::Result")),
               "",
               Some(R.RawExpr("write!(_formatter, \"" + c.enclosingModule.id + "." + c.name + "\")"))
             ))]
        );
      var printImpl := [R.ImplDecl(p)];

      var pp := R.ImplFor(
        sTypeParams,
        R.RawType("::std::cmp::PartialEq"),
        R.TypeApp(R.TIdentifier(datatypeName), typeParamsAsTypes),
        "",
        [R.FnDecl(
           R.PRIV,
           R.Fn(
             "eq", [],
             [R.Formal.selfBorrowed, R.Formal("other", R.SelfBorrowed)],
             Some(R.Type.Bool),
             "",
             Some(R.RawExpr("::std::ptr::eq(self, other)"))
           ))]
      );
      var ptrPartialEqImpl := [R.ImplDecl(pp)];

      s := s + defaultImpl + printImpl + ptrPartialEqImpl;
    }

    static method GenTrait(t: Trait, containingPath: seq<Ident>) returns (s: string) {
      var typeParamsSet := {};
      var typeParams := [];
      var tpI := 0;
      if |t.typeParams| > 0 {
        while tpI < |t.typeParams| {
          var tp := t.typeParams[tpI];
          typeParamsSet := typeParamsSet + {tp};
          var genTp := GenType(tp, false, false);
          typeParams := typeParams + [genTp];
          tpI := tpI + 1;
        }
      }

      var fullPath := containingPath + [Ident.Ident(t.name)];
      var implBody, _ := GenClassImplBody(t.body, true, Type.Path(fullPath, [], ResolvedType.Trait(fullPath, t.attributes)), typeParamsSet);
      s :=
        R.TraitDecl(R.Trait(
                      [], R.TypeApp(R.TIdentifier(escapeIdent(t.name)), typeParams),
                      "",
                      implBody
                    )).ToString(IND);
    }

    static method GenNewtype(c: Newtype) returns (s: seq<R.ModDecl>) {
      var typeParamsSet, sTypeParams, sConstrainedTypeParams, whereConstraints := GenTypeParameters(c.typeParams);
      var typeParamsAsTypes :=
        Std.Collections.Seq.Map((t: R.TypeParam) => R.RawType(t.content), sTypeParams);
      var constrainedTypeParams := R.TypeParam.ToStringMultiple(sConstrainedTypeParams, R.IND + R.IND);

      var underlyingType;
      match NewtypeToRustType(c.base, c.range) {
        case Some(v) =>
          underlyingType := v;
        case None =>
          underlyingType := GenType(c.base, false, false);
      }
      var resultingType :=
        Path([], [], ResolvedType.Newtype(c.base, c.range, false, c.attributes));
      var datatypeName := escapeIdent(c.name);
      s := [
        R.StructDecl(
          R.Struct(
            [
              R.RawAttribute("#[derive(Clone, PartialEq)]"),
              R.RawAttribute("#[repr(transparent)]")
            ],
            datatypeName,
            sTypeParams,
            R.NamelessFields([R.NamelessField(R.PUB, underlyingType)])
          ))];

      var fnBody := R.Identifier(datatypeName);

      match c.witnessExpr {
        case Some(e) => {
          var e := if c.base == resultingType then e else Convert(e, c.base, resultingType);
          // TODO(Mikael): generate statements if any
          var eStr, _, _ := GenExpr(e, None, Environment.Empty(), OwnershipOwned);
          fnBody := fnBody.Apply1(eStr);
        }
        case None => {
          fnBody := fnBody.Apply1(R.std_Default_default);
        }
      }

      var body :=
        R.FnDecl(
          R.PRIV,
          R.Fn(
            "default", [], [], Some(R.SelfOwned),
            "",
            Some(fnBody)
          ));
      s := s + [
        R.ImplDecl(
          R.ImplFor(
            sConstrainedTypeParams,
            R.DefaultTrait,
            R.TypeApp(R.TIdentifier(datatypeName), typeParamsAsTypes),
            whereConstraints,
            [body]))];
      s := s + [
        R.ImplDecl(
          R.ImplFor(
                     sConstrainedTypeParams,
                     R.DafnyPrintTrait,
                     R.TypeApp(R.TIdentifier(datatypeName), typeParamsAsTypes),
                     "",
                     [R.FnDecl(
                      R.PRIV,
                               R.Fn("fmt_print", [],
                                    [R.Formal.selfBorrowed, R.Formal("_formatter", R.RawType("&mut ::std::fmt::Formatter")), R.Formal("in_seq", R.Type.Bool)],
                                    Some(R.RawType("::std::fmt::Result")),
                                    "",
                                    Some(R.RawExpr("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))
                               ))]))];
      s := s + [
        R.ImplDecl(
          R.ImplFor(
            sConstrainedTypeParams,
            R.RawType("::std::ops::Deref"),
            R.TypeApp(R.TIdentifier(datatypeName), typeParamsAsTypes),
            "",
            [R.RawImplMember("type Target = " + underlyingType.ToString(IND) + ";"),
             R.FnDecl(
               R.PRIV,
               R.Fn("deref", [],
                    [R.Formal.selfBorrowed], Some(R.SelfBorrowed.MSel("Target")),
                    "",
                    Some(R.RawExpr("&self.0"))))]))];
    }

    static method GenDatatype(c: Datatype) returns (s: seq<R.ModDecl>) {
      var typeParamsSet, sTypeParams, sConstrainedTypeParams, whereConstraints := GenTypeParameters(c.typeParams);
      var typeParamsAsTypes :=
        Std.Collections.Seq.Map((t: R.TypeParam) => R.RawType(t.content), sTypeParams);
      var constrainedTypeParams := R.TypeParam.ToStringMultiple(sConstrainedTypeParams, IND + IND);

      var datatypeName := escapeIdent(c.name);
      var ctors: seq<R.EnumCase> := [];
      var i := 0;
      while i < |c.ctors| {
        var ctor := c.ctors[i];
        var ctorArgs: seq<R.Field> := [];
        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          var formalType := GenType(formal.typ, false, false);
          if c.isCo {
            ctorArgs := ctorArgs + [
              R.Field(R.PRIV,
              R.Formal(escapeIdent(formal.name),
                       R.TypeApp(R.dafny_runtime_type.MSel("LazyFieldWrapper"), [formalType])))];
          } else {
            ctorArgs := ctorArgs + [
              R.Field(R.PRIV,
              R.Formal(escapeIdent(formal.name), formalType))];
          }
          j := j + 1;
        }
        ctors := ctors + [R.EnumCase(escapeIdent(ctor.name), R.NamedFields(ctorArgs))];
        i := i + 1;
      }

      var selfPath := [Ident.Ident(c.name)];
      var implBodyRaw, traitBodies := GenClassImplBody(c.body, false, Type.Path([], [], ResolvedType.Datatype(DatatypeType(selfPath, c.attributes))), typeParamsSet);
      var implBody: seq<R.ImplMember> := implBodyRaw;
      i := 0;
      var emittedFields: set<string> := {};
      while i < |c.ctors| {
        // we know that across all ctors, each any fields with the same name have the same type
        // so we want to emit methods for each field that pull the appropriate value given
        // the current variant (and panic if we have a variant with no such field)
        var ctor := c.ctors[i];
        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          if !(formal.name in emittedFields) {
            emittedFields := emittedFields + {formal.name};

            var formalType := GenType(formal.typ, false, false);
            var cases: seq<R.MatchCase> := [];
            var k := 0;
            while k < |c.ctors| {
              var ctor2 := c.ctors[k];

              var pattern := datatypeName + "::" + escapeIdent(ctor2.name) + " { ";
              var rhs: string;
              var l := 0;
              var hasMatchingField := false;
              while l < |ctor2.args| {
                var formal2 := ctor2.args[l];
                if formal.name == formal2.name {
                  hasMatchingField := true;
                }
                pattern := pattern + escapeIdent(formal2.name) + ", ";
                l := l + 1;
              }

              pattern := pattern + "}";

              if hasMatchingField {
                if c.isCo {
                  rhs := "::std::ops::Deref::deref(&" + escapeIdent(formal.name) + ".0)";
                } else {
                  rhs := escapeIdent(formal.name) + "";
                }
              } else {
                rhs := "panic!(\"field does not exist on this variant\")";
              }
              var ctorMatch := R.MatchCase(R.RawPattern(pattern), R.RawExpr(rhs));
              cases := cases + [ctorMatch];
              k := k + 1;
            }

            if |c.typeParams| > 0 {
              cases := cases + [
                R.MatchCase(R.RawPattern(datatypeName + "::_PhantomVariant(..)"), R.RawExpr("panic!()"))
              ];
            }

            var methodBody := R.Match(
              R.self,
              cases
            );

            implBody := implBody + [
              R.FnDecl(
                R.PUB,
                R.Fn(
                  escapeIdent(formal.name),
                  [], [R.Formal.selfBorrowed], Some(R.Borrowed(formalType)),
                  "",
                  Some(methodBody)
                ))];
          }
          j := j + 1;
        }

        i := i + 1;
      }

      if |c.typeParams| > 0 {
        var typeI := 0;
        var types: seq<R.Type> := [];
        while typeI < |c.typeParams| {
          var genTp := GenType(c.typeParams[typeI], false, false);
          types := types + [R.TypeApp(R.TIdentifier("::std::marker::PhantomData::"), [genTp])];
          typeI := typeI + 1;
        }
        ctors := ctors + [R.EnumCase("_PhantomVariant",
                                     R.NamelessFields(Std.Collections.Seq.Map(
                                                         tpe => R.NamelessField(R.PRIV, tpe), types))
                          )];
      }
      var enumBody :=
        [R.EnumDecl(
           R.Enum([R.RawAttribute("#[derive(PartialEq, Clone)]")],
                  datatypeName,
                  sTypeParams,
                  ctors
           )),
         R.ImplDecl(
           R.Impl(
             sConstrainedTypeParams,
             R.TypeApp(R.TIdentifier(datatypeName), typeParamsAsTypes),
             whereConstraints,
             implBody
           ))];

      i := 0;
      var printImplBodyCases: seq<R.MatchCase> := [];
      while i < |c.ctors| {
        var ctor := c.ctors[i];
        var ctorMatch := escapeIdent(ctor.name) + " { ";

        var modulePrefix := if c.enclosingModule.id == "_module" then "" else c.enclosingModule.id + ".";
        var printRhs :=
          R.RawExpr("write!(_formatter, \"" + modulePrefix + c.name + "." + escapeIdent(ctor.name) + (if ctor.hasAnyArgs then "(\")?" else "\")?"));

        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          ctorMatch := ctorMatch + escapeIdent(formal.name) + ", ";

          if (j > 0) {
            printRhs := printRhs.Then(R.RawExpr("write!(_formatter, \", \")?"));
          }
          printRhs := printRhs.Then(R.RawExpr("::dafny_runtime::DafnyPrint::fmt_print(" + escapeIdent(formal.name) + ", _formatter, false)?"));

          j := j + 1;
        }

        ctorMatch := ctorMatch + "}";

        if (ctor.hasAnyArgs) {
          printRhs := printRhs.Then(R.RawExpr("write!(_formatter, \")\")?"));
        }

        printRhs := printRhs.Then(R.RawExpr("Ok(())"));

        printImplBodyCases := printImplBodyCases + [
          R.MatchCase(R.RawPattern(datatypeName + "::" + ctorMatch),
                      R.Block(printRhs))
        ];
        i := i + 1;
      }

      if |c.typeParams| > 0 {
        printImplBodyCases := printImplBodyCases + [
          R.MatchCase(R.RawPattern(datatypeName + "::_PhantomVariant(..)"), R.RawExpr("{panic!()}"))
        ];
      }
      var printImplBody := R.Match(
        R.self,
        printImplBodyCases);
      var printImpl := [
        R.ImplDecl(
          R.ImplFor(
            sConstrainedTypeParams,
            R.DafnyPrintTrait,
            R.TypeApp(R.TIdentifier(datatypeName), typeParamsAsTypes),
            "",
            [R.FnDecl(
               R.PRIV,
               R.Fn(
                 "fmt_print", [],
                 [R.Formal.selfBorrowed, R.Formal("_formatter", R.RawType("&mut ::std::fmt::Formatter")), R.Formal("_in_seq", R.Type.Bool)],
                 Some(R.RawType("std::fmt::Result")),
                 "",
                 Some(printImplBody)))]
          ))];

      var defaultImpl := [];
      var asRefImpl := [];
      if |c.ctors| > 0 {
        i := 0;
        var structName := R.Identifier(datatypeName).MSel(escapeIdent(c.ctors[0].name));
        var structAssignments: seq<R.AssignIdentifier> := [];
        while i < |c.ctors[0].args| {
          var formal := c.ctors[0].args[i];
          structAssignments := structAssignments + [
            R.AssignIdentifier(escapeIdent(formal.name), R.RawExpr("::std::default::Default::default()"))
          ];
          i := i + 1;
        }
        var defaultConstrainedTypeParams := R.TypeParam.AddConstraintsMultiple(
          sTypeParams, [R.DefaultTrait]
        );
        var fullType := R.TypeApp(R.TIdentifier(datatypeName), typeParamsAsTypes);
        defaultImpl := [
          R.ImplDecl(
            R.ImplFor(
              defaultConstrainedTypeParams,
              R.DefaultTrait,
              fullType,
              "",
              [R.FnDecl(
                 R.PRIV,
                 R.Fn("default", [], [], Some(fullType),
                      "",
                      Some(R.StructBuild(
                             structName,
                             structAssignments
                           )))
               )]
            ))];
        asRefImpl := [
        R.ImplDecl(
          R.ImplFor(
            defaultConstrainedTypeParams,
            R.std_type.MSel("convert").MSel("AsRef").Apply1(fullType),
            R.Borrowed(fullType),
            "",
            [R.FnDecl(
                R.PRIV,
                R.Fn("as_ref", [], [R.Formal.selfBorrowed], Some(R.SelfOwned),
                    "",
                    Some(R.self))
              )]
          ))];
      }
      s := enumBody + printImpl + defaultImpl + asRefImpl;
    }

    static method GenPath(p: seq<Ident>) returns (r: R.Type) {
      if |p| == 0 {
        return R.SelfOwned;
      } else {
        // TODO: Better distinction between Dafny modules and any module
        r := if p[0].id == "std" then R.TIdentifier("") else R.TIdentifier("super");
        for i := 0 to |p| {
          r := r.MSel(escapeIdent(p[i].id));
        }
      }
    }

    static method GenPathExpr(p: seq<Ident>) returns (r: R.Expr) {
      if |p| == 0 {
        return R.self;
      } else {
        r := if p[0].id == "std" then R.Identifier("") else R.Identifier("super");
        for i := 0 to |p| {
          r := r.MSel(escapeIdent(p[i].id));
        }
      }
    }

    static method GenTypeArgs(args: seq<Type>, inBinding: bool, inFn: bool) returns (s: seq<R.Type>) {
      s := [];
      if |args| > 0 {
        var i := 0;
        while i < |args| {
          var genTp := GenType(args[i], inBinding, inFn);
          s := s + [genTp];
          i := i + 1;
        }
      }
    }

    static predicate IsRcWrapped(attributes: seq<Attribute>) {
      (Attribute("auto-nongrowing-size", []) !in attributes &&
       Attribute("rust_rc", ["false"]) !in attributes) ||
      Attribute("rust_rc", ["true"]) in attributes
    }

    static method GenType(c: Type, inBinding: bool, inFn: bool) returns (s: R.Type) {
      match c {
        case Path(p, args, resolved) => {
          var t := GenPath(p);
          var typeArgs := GenTypeArgs(args, inBinding, inFn);
          s := R.TypeApp(t, typeArgs);

          match resolved {
            case AllocatedDatatype(DatatypeType(_, attributes)) => {
              s := R.PointerMut(s);
            }
            case Datatype(DatatypeType(_, attributes)) => {
              if IsRcWrapped(attributes) {
                s := R.Rc(s);
              }
            }
            case Trait(_, _) => {
              if p == [Ident.Ident("_System"), Ident.Ident("object")] {
                s := R.PointerMut(R.DynType(R.std_type.MSel("any").MSel("Any")));
              } else {
                if inBinding {
                  // impl trait in bindings is not stable
                  s := R.RawType("_");
                } else {
                  s := R.ImplType(s);
                }
              }
            }
            case Newtype(t, range, erased, attributes) => {
              if erased {
                match NewtypeToRustType(t, range) {
                  case Some(v) =>
                    s := v;
                  case None =>
                }
              }
            }
          }
        }
        case Nullable(inner) => {
          var innerExpr := GenType(inner, inBinding, inFn);
          s := R.TypeApp(R.TIdentifier("::std::option::Option"), [innerExpr]);
        }
        case Tuple(types) => {
          var args := [];
          var i := 0;
          while i < |types| {
            var generated := GenType(types[i], inBinding, inFn);
            args := args + [generated];
            i := i + 1;
          }
          s := R.TupleType(args);
        }
        case Array(element, dims) => {
          var elem := GenType(element, inBinding, inFn);
          s := elem;
          var i := 0;
          while i < dims {
            s := R.Rc(R.RefCell(R.Vec(s)));
            i := i + 1;
          }
        }
        case Seq(element) => {
          var elem := GenType(element, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("Sequence"), [elem]);
        }
        case Set(element) => {
          var elem := GenType(element, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("Set"), [elem]);
        }
        case Multiset(element) => {
          var elem := GenType(element, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("Multiset"), [elem]);
        }
        case Map(key, value) => {
          var keyType := GenType(key, inBinding, inFn);
          var valueType := GenType(value, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("Map"), [keyType, valueType]);
        }
        case MapBuilder(key, value) => {
          var keyType := GenType(key, inBinding, inFn);
          var valueType := GenType(value, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("MapBuilder"), [keyType, valueType]);
        }
        case SetBuilder(elem) => {
          var elemType := GenType(elem, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("SetBuilder"), [elemType]);
        }
        case Arrow(args, result) => {
          // we cannot use impl until Rc<Fn> impls Fn
          // if inFn || inBinding {
          //  s := "::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(";
          // } else {
          //   s := "::dafny_runtime::FunctionWrapper<impl ::std::ops::Fn(";
          // }
          var argTypes := [];
          var i := 0;
          while i < |args| {

            var generated := GenType(args[i], inBinding, true);
            argTypes := argTypes + [R.Borrowed(generated)];
            i := i + 1;
          }

          var resultType := GenType(result, inBinding, inFn || inBinding);
          s := R.TypeApp(
            R.dafny_runtime_type.MSel("FunctionWrapper"),
            [R.FnType(argTypes, R.IntersectionType(resultType, R.StaticTrait))]);

          // if inFn || inBinding {
          //s := s + ") -> " + resultType + " + 'static>>";
          // } else {
          //   s := s + ") -> " + resultType + " + Clone + 'static>";
          // }
        }
        case TypeArg(Ident(name)) => s := R.RawType(escapeIdent(name));
        case Primitive(p) => {
          match p {
            case Int => s := R.dafny_runtime_type.MSel("DafnyInt");
            case Real => s := R.dafny_runtime_type.MSel("BigRational");
            case String => s := R.TypeApp(R.dafny_runtime_type.MSel("Sequence"),
                                          [R.dafny_runtime_type.MSel(DafnyChar)]);
            case Bool => s := R.Type.Bool;
            case Char => s := R.dafny_runtime_type.MSel(DafnyChar);
          }
        }
        case Passthrough(v) => s := R.RawType(v);
      }
    }

    static method GenClassImplBody(body: seq<ClassItem>, forTrait: bool, enclosingType: Type, enclosingTypeParams: set<Type>)
      returns (s: seq<R.ImplMember>, traitBodies: map<seq<Ident>, seq<R.ImplMember>>)
    {
      s := [];
      traitBodies := map[];

      var i := 0;
      while i < |body| {
        match body[i] {
          case Method(m) => {
            match m.overridingPath {
              case Some(p) => {
                var existing: seq<R.ImplMember> := [];
                if p in traitBodies {
                  existing := traitBodies[p];
                }

                var genMethod := GenMethod(m, true, enclosingType, enclosingTypeParams);
                existing := existing + [genMethod];

                traitBodies := traitBodies + map[p := existing];
              }
              case None => {
                var generated := GenMethod(m, forTrait, enclosingType, enclosingTypeParams);
                s := s + [generated];
              }
            }
          }
        }
        i := i + 1;
      }
    }

    static method GenParams(params: seq<Formal>) returns (s: seq<R.Formal>)
      ensures |s| == |params|
    {
      s := [];
      var i := 0;
      while i < |params| invariant |s| == i && i <= |params| {
        var param := params[i];
        var paramType := GenType(param.typ, false, false);
        if !paramType.HasCopySemantics() {
          paramType := R.Borrowed(paramType);
        }
        s := s + [R.Formal(escapeIdent(param.name), paramType)];
        i := i + 1;
      }
    }

    static method GenMethod(m: Method, forTrait: bool, enclosingType: Type, enclosingTypeParams: set<Type>) returns (s: R.ImplMember) {
      var params: seq<R.Formal> := GenParams(m.params);
      var paramNames := [];
      var paramTypes := map[];
      for paramI := 0 to |m.params| {
        var dafny_formal := m.params[paramI];
        var formal := params[paramI];
        var name := formal.name;
        paramNames := paramNames + [name];
        paramTypes := paramTypes[name := formal.tpe];
      }
      var fnName := escapeIdent(m.name);

      var selfIdentifier: Option<string> := None;

      if (!m.isStatic) {
        var selfId := "self";
        if fnName == "_ctor" { // Constructors take a raw pointer, which is not accepted as a self type in Rust
          selfId := "this";
        }
        if (forTrait) {
          var selfFormal := if m.wasFunction then R.Formal.selfBorrowed else R.Formal.selfBorrowedMut;
          params := [selfFormal] + params;
        } else {
          var tpe := GenType(enclosingType, false, false);
          if !tpe.HasCopySemantics() {
            tpe := R.Borrowed(tpe);
          }
          // Special case, pointers receive 
          if selfId == "self" {
            if tpe.IsSelfPointer() {
              if m.wasFunction {
                tpe := R.SelfBorrowed;
              } else {
                tpe := R.SelfBorrowedMut;
              }
            } else {
                print "#### Weird this type: ", tpe, "\n";
            }
          }
          params := [R.Formal(selfId, tpe)] + params;
        }
        selfIdentifier := Some(selfId);
      }

      // TODO: Use mut instead of a tuple for the API of multiple output parameters
      var retTypeArgs := [];
      //var retType := if |m.outTypes| != 1 then "(" else "";

      var typeI := 0;
      while typeI < |m.outTypes| {
        var typeExpr := GenType(m.outTypes[typeI], false, false);
        retTypeArgs := retTypeArgs + [typeExpr];

        typeI := typeI + 1;
      }

      var visibility := R.PUB;//if forTrait then R.PUB else R.PRIV;

      var typeParamsFiltered := [];
      for typeParamI := 0 to |m.typeParams| {
        var typeParam := m.typeParams[typeParamI];
        if !(typeParam in enclosingTypeParams) {
          typeParamsFiltered := typeParamsFiltered + [typeParam];
        }
      }

      var whereClauses := "";

      var typeParams: seq<R.TypeParam> := [];

      if (|typeParamsFiltered| > 0) {
        whereClauses := whereClauses + " where ";

        var i := 0;
        while i < |typeParamsFiltered| {

          var typeExpr := GenType(typeParamsFiltered[i], false, false);
          typeParams := typeParams + [
            R.RawTypeParam(typeExpr.ToString(IND),
                           [R.CloneTrait,
                            R.DafnyPrintTrait,
                            R.DefaultTrait,
                            R.StaticTrait])
          ];

          i := i + 1;
        }
      }

      var fBody: Option<R.Expr>;
      var env: Environment;
      var preBody := R.RawExpr("");
      var preAssignNames: seq<string> := [];
      var preAssignTypes: map<string, R.Type> := map[];

      if m.hasBody {
        var earlyReturn: R.Expr := R.Return(None);
        match m.outVars {
          case Some(outVars) => {
            if m.outVarsAreUninitFieldsToAssign {
              earlyReturn := R.Return(Some(R.Tuple([])));
              for outI := 0 to |outVars| {
                var outVar := outVars[outI];
                var outName := escapeIdent(outVar.id);
                var tracker_name := AddAssignedPrefix(outName);
                preAssignNames := preAssignNames + [tracker_name];
                preAssignTypes := preAssignTypes[tracker_name := R.Type.Bool];

                preBody := preBody.Then(R.DeclareVar(R.MUT, tracker_name, Some(R.Type.Bool), Some(R.LiteralBool(false))));
              }
            } else {
              var tupleArgs := [];
              assume {:axiom} |m.outTypes| == |outVars|;

              for outI := 0 to |outVars| {
                var outVar := outVars[outI];
                var outType := GenType(m.outTypes[outI], false, false);
                var outName := escapeIdent(outVar.id);
                paramNames := paramNames + [outName];
                var outMaybeType := if outType.HasCopySemantics() then outType else R.MaybePlaceboType(outType);
                paramTypes := paramTypes[outName := outMaybeType];

                var outVarReturn, _, _ := GenExpr(Expression.Ident(outVar.id), None,
                  Environment([outName], map[outName := outMaybeType]), OwnershipOwned);
                tupleArgs := tupleArgs + [outVarReturn];
              }
              if |tupleArgs| == 1 {
                earlyReturn := R.Return(Some(tupleArgs[0]));
              } else {
                earlyReturn := R.Return(Some(R.Tuple(tupleArgs)));
              }
            }
          }
          case None => {}
        }
        env := Environment(preAssignNames + paramNames, preAssignTypes + paramTypes);

        var body, _, _ := GenStmts(m.body, selfIdentifier, env, true, earlyReturn);

        fBody := Some(preBody.Then(body));
      } else {
        env := Environment(paramNames, paramTypes);
        fBody := None;
      }
      s := R.FnDecl(
        visibility,
        R.Fn(
          fnName,
          typeParams,
          params,
          Some(if |retTypeArgs| == 1 then retTypeArgs[0] else R.TupleType(retTypeArgs)),
          whereClauses,
          fBody
        )
      );
    }

    static method GenStmts(stmts: seq<Statement>, selfIdent: Option<string>, env: Environment, isLast: bool, earlyReturn: R.Expr) returns (generated: R.Expr, readIdents: set<string>, newEnv: Environment)
      decreases stmts, 1, 0
    {
      generated := R.RawExpr("");
      var declarations := {};
      readIdents := {};
      var i := 0;
      newEnv := env;
      ghost var oldStmts := stmts;
      var stmts := stmts; // Make it mutable
      while i < |stmts| {
        var stmt := stmts[i];
        // Avoid lazy initialization if it is not necessary
        match stmt {
          case DeclareVar(name, optType, None) =>
            if i + 1< |stmts| {
              match stmts[i + 1] {
                case Assign(Ident(Ident(name2)), rhs) =>
                  if name2 == name {
                    stmts := stmts[0..i] + [DeclareVar(name, optType, Some(rhs))] + stmts[i+1..];
                    stmt := stmts[i];
                  }
                case _ =>
              }
            }
          case _ =>

        }
        assume {:axiom} stmt in oldStmts;
        var stmtExpr, recIdents, newEnv2 := GenStmt(stmt, selfIdent, newEnv, isLast && (i == |stmts| - 1), earlyReturn);
        readIdents := readIdents + (recIdents - declarations);
        newEnv := newEnv2;

        match stmt {
          case DeclareVar(name, _, _) => {
            declarations := declarations + {name};
          }
          case _ => {}
        }
        generated := generated.Then(stmtExpr);

        i := i + 1;
      }
    }

    static method GenAssignLhs(lhs: AssignLhs, rhs: R.Expr, selfIdent: Option<string>, env: Environment) returns (generated: R.Expr, needsIIFE: bool, readIdents: set<string>, newEnv: Environment)
      decreases lhs, 1
    {
      newEnv := env;
      match lhs {
        case Ident(Ident(id)) => {
          var idRust := escapeIdent(id);
          if env.IsBorrowed(idRust) || env.IsBorrowedMut(idRust) {
            generated := R.AssignVar("*" + idRust, rhs);
          } else {
            generated := R.AssignVar(idRust, rhs);
          }

          readIdents := {id};
          needsIIFE := false;
        }

        case Select(on, field) => {
          var fieldName := escapeIdent(field);
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowedMut);
          print "Environment: ", env, ", on = ", on, "\n";
          print "Select on GenAssignLhs: ", lhs, ", fieldName =", fieldName, ", onExpr=", onExpr, "\n";
          generated := 
            R.AssignMember(onExpr, fieldName, rhs);
          match onExpr { // Particular case of the constructor, we don't want the previous value to be dropped if it's assigned the first time
            case UnaryOp("&mut", Identifier("this"), _) | Identifier("this") =>
              var isAssignedVar := AddAssignedPrefix(fieldName);
              if isAssignedVar in newEnv.names {
                generated := R.dafny_runtime.MSel("update_field_uninit!").Apply([
                  R.Identifier("this"), R.Identifier(fieldName), R.Identifier(isAssignedVar), rhs]);
                newEnv := newEnv.RemoveAssigned(isAssignedVar);
              }
            case _ =>
          }
          readIdents := recIdents;
          needsIIFE := false;
        }

        case Index(on, indices) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
          readIdents := recIdents;

          var s := "{\n";

          var i := 0;
          while i < |indices| {
            var idx, _, recIdentsIdx := GenExpr(indices[i], selfIdent, env, OwnershipOwned);

            s := s + "let __idx" + Strings.OfNat(i) + " = <usize as ::dafny_runtime::NumCast>::from(" + idx.ToString(IND) + ").unwrap();\n";

            readIdents := readIdents + recIdentsIdx;

            i := i + 1;
          }

          s := s + onExpr.ToString(IND) + ".borrow_mut()";
          i := 0;
          while i < |indices| {
            s := s + "[__idx" + Strings.OfNat(i) + "]";
            i := i + 1;
          }

          s := s + " = " + rhs.ToString(IND) + ";\n}";
          generated := R.RawExpr(s);
          needsIIFE := true;
        }
      }
    }

    static method GenStmt(stmt: Statement, selfIdent: Option<string>, env: Environment, isLast: bool, earlyReturn: R.Expr) returns (generated: R.Expr, readIdents: set<string>, newEnv: Environment)
      decreases stmt, 1, 1
    {
      match stmt {
        case ConstructorNewSeparator(fields) => {
          generated := R.RawExpr("");
          readIdents := {};
          newEnv := env;
          for i := 0 to |fields| {
            var fieldName := escapeIdent(fields[0].name);
            var fieldTyp := GenType(fields[0].typ, false, false);
            var isAssignedVar := AddAssignedPrefix(fieldName);
            if isAssignedVar in newEnv.names {
              assume {:axiom} InitializationValue(fields[0].typ) < stmt; // Needed for termination
              var rhs, _, _ := GenExpr(InitializationValue(fields[0].typ), selfIdent, env, OwnershipOwned);
              readIdents := readIdents + {isAssignedVar};
              generated := generated.Then(R.dafny_runtime.MSel("update_field_if_uninit!").Apply([
                  R.Identifier("this"), R.Identifier(fieldName), R.Identifier(isAssignedVar), rhs]));
              newEnv := newEnv.RemoveAssigned(isAssignedVar);
            }
          }
        }
        case DeclareVar(name, typ, Some(expression)) => {
          var tpe := GenType(typ, true, false);
          var varName := escapeIdent(name);
          var hasCopySemantics := tpe.HasCopySemantics();
          if expression.InitializationValue? && !hasCopySemantics {
            generated := R.DeclareVar(R.MUT, varName, None, Some(R.dafny_runtime.MSel("MaybePlacebo").ApplyType1(tpe).MSel("new").Apply([])));
            readIdents := {};
            newEnv := env.AddAssigned(varName, R.MaybePlaceboType(tpe));
          } else {
            var expr, recIdents;
            if expression.InitializationValue? && 
                      (|| tpe.Pointer?
                       || tpe.PointerMut?) {
              expr := R.std.MSel("ptr").MSel("null_mut").Apply([]);
              recIdents := {};
            } else {
              var exprOwnership;
              expr, exprOwnership, recIdents := GenExpr(expression, selfIdent, env, OwnershipOwned);
            }
            readIdents := recIdents;
            generated := R.DeclareVar(R.MUT, escapeIdent(name), Some(tpe), Some(expr));
            newEnv := env.AddAssigned(escapeIdent(name), tpe);
          }
        }
        case DeclareVar(name, typ, None) => {
          var newStmt := DeclareVar(name, typ, Some(InitializationValue(typ)));
          assume {:axiom} newStmt < stmt;
          generated, readIdents, newEnv := GenStmt(newStmt, selfIdent, env, isLast, earlyReturn);
        }
        case Assign(lhs, expression) => {
          var exprGen, _, exprIdents := GenExpr(expression, selfIdent, env, OwnershipOwned);
          if lhs.Ident? {
            var rustId := escapeIdent(lhs.ident.id);
            var tpe := env.GetType(rustId);
            if tpe.Some? && tpe.value.ExtractMaybePlacebo().Some? {
              exprGen := R.MaybePlacebo(exprGen);
            }
          }
          var lhsGen, needsIIFE, recIdents, resEnv := GenAssignLhs(lhs, exprGen, selfIdent, env);
          generated := lhsGen;
          newEnv := resEnv;

          if needsIIFE {
            generated := R.Block(generated);
          }
          readIdents := recIdents + exprIdents;
        }
        case If(cond, thnDafny, elsDafny) => {
          var cond, _, recIdents := GenExpr(cond, selfIdent, env, OwnershipOwned);
          var condString := cond.ToString(IND);

          readIdents := recIdents;
          var thn, thnIdents, thnEnv := GenStmts(thnDafny, selfIdent, env, isLast, earlyReturn);
          readIdents := readIdents + thnIdents;
          var els, elsIdents, elsEnv := GenStmts(elsDafny, selfIdent, env, isLast, earlyReturn);
          readIdents := readIdents + elsIdents;
          newEnv := env;
          generated := R.IfExpr(cond, thn, els);
        }
        case Labeled(lbl, body) => {
          var body, bodyIdents, env2 := GenStmts(body, selfIdent, env, isLast, earlyReturn);
          readIdents := bodyIdents;
          generated := R.Labelled("label_" + lbl, R.Loop(None, R.StmtExpr(body, R.Break(None))));
          newEnv := env;
        }
        case While(cond, body) => {
          var cond, _, recIdents := GenExpr(cond, selfIdent, env, OwnershipOwned);
          readIdents := recIdents;

          var bodyExpr, bodyIdents, bodyEnv := GenStmts(body, selfIdent, env, false, earlyReturn);

          newEnv := env;
          readIdents := readIdents + bodyIdents;
          generated := R.Loop(Some(cond), bodyExpr);
        }
        case Foreach(boundName, boundType, over, body) => {
          var over, _, recIdents := GenExpr(over, selfIdent, env, OwnershipOwned);

          var boundTpe := GenType(boundType, false, false);

          readIdents := recIdents;
          var bodyExpr, bodyIdents, bodyEnv := GenStmts(body, selfIdent, env.AddAssigned(boundName, R.Borrowed(boundTpe)), false, earlyReturn);
          readIdents := readIdents + bodyIdents - {boundName};
          newEnv := env;
          generated := R.For(escapeIdent(boundName), over, bodyExpr);
        }
        case Break(toLabel) => {
          match toLabel {
            case Some(lbl) => {
              generated := R.Break(Some("label_" + lbl));
            }
            case None => {
              generated := R.Break(None);
            }
          }
          readIdents := {};
          newEnv := env;
        }
        case TailRecursive(body) => {
          // clone the parameters to make them mutable
          generated := R.RawExpr("");

          if selfIdent != None {
            generated := generated.Then(R.DeclareVar(R.MUT, "_this", None, Some(R.self.Sel("clone").Apply([]))));
          }

          for paramI := 0 to |env.names| {
            var param := env.names[paramI];
            assume {:axiom} Expression.Ident(param) < stmt;
            var paramInit, _, _ := GenExpr(Expression.Ident(param), selfIdent, env, OwnershipOwned);
            generated := generated.Then(R.DeclareVar(R.MUT, escapeIdent(param), None, Some(paramInit)));
          }
          var bodyExpr, bodyIdents, bodyEnv := GenStmts(body, if selfIdent != None then Some("_this") else None, env, false, earlyReturn);
          newEnv := env;
          readIdents := bodyIdents;
          generated := generated.Then(
                         R.Labelled("TAIL_CALL_START",
                           R.Loop(None, bodyExpr)));
        }
        case JumpTailCallStart() => {
          generated := R.Continue(Some("TAIL_CALL_START"));
          readIdents := {};
          newEnv := env;
        }
        case Call(on, name, typeArgs, args, maybeOutVars) => {
          readIdents := {};

          var onExpr, _, enclosingIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);

          var typeExprs := [];
          if (|typeArgs| >= 1) {
            var typeI := 0;
            var typeArgsR := [];
            while typeI < |typeArgs| {
              var tpe := GenType(typeArgs[typeI], false, false);
              typeArgsR := typeArgsR + [tpe];

              typeI := typeI + 1;
            }
          }

          var argExprs := [];
          for i := 0 to |args| {
            var argOwnership := OwnershipBorrowed;
            if name.Name? && i < |name.signature.parameters| {
              var tpe := GenType(name.signature.parameters[i].typ, false, false);
              if tpe.HasCopySemantics() {
                argOwnership := OwnershipOwned;
              }
            }
            var argExpr, ownership, argIdents := GenExpr(args[i], selfIdent, env, argOwnership);
            argExprs := argExprs + [argExpr];
            readIdents := readIdents + argIdents;
          }
          readIdents := readIdents + enclosingIdents;
          
          var renderedName := match name {
            case Name(name, _, _) => escapeIdent(name)
            case MapBuilderAdd() | SetBuilderAdd() => "add"
            case MapBuilderBuild() | SetBuilderBuild() => "build"
          };
          match on {
            case Companion(_) => {
              onExpr := onExpr.MSel(renderedName);
            }
            case _ => {
              match name {
                case Name(_, Some(tpe), _) =>
                  var typ := GenType(tpe, false, false);
                  if typ.Pointer? || typ.PointerMut? {
                    onExpr := R.dafny_runtime.MSel("modify!").Apply1(onExpr);
                  }
                case _ =>
              }
              onExpr := onExpr.Sel(renderedName);
            }
          }
          generated := onExpr;
          if |typeExprs| > 0 {
            generated := generated.ApplyType(typeExprs);
          }
          generated := generated.Apply(argExprs);

          if maybeOutVars.Some? && |maybeOutVars.value| == 1 {
            var outVar := maybeOutVars.value[0].id;
            if !env.HasCopySemantics(outVar) {
              generated := R.MaybePlacebo(generated);
            }
            generated := R.AssignVar(outVar, generated);
          } else if maybeOutVars.None? || |maybeOutVars.value| == 0 {
            // Nothing to do here.
          } else { // Multiple variables
            var tmpVar := "_x";
            var tmpId := R.Identifier(tmpVar);
            generated := R.DeclareVar(R.CONST, tmpVar, None, Some(generated));
            // We emit assignment to each receiver depending on its type, if it could be a placebo or not.
            var outVars := maybeOutVars.value;
            for outI := 0 to |outVars| {
              var outVar := outVars[outI].id;
              var rhs := tmpId.Sel(Strings.OfNat(outI));
              if !env.HasCopySemantics(outVar) { 
                rhs := R.MaybePlacebo(rhs);
              }
              generated := generated.Then(R.AssignVar(outVar, rhs));
            }
          }
          newEnv := env;
        }
        case Return(exprDafny) => {
          var expr, _, recIdents := GenExpr(exprDafny, selfIdent, env, OwnershipOwned);
          readIdents := recIdents;

          if isLast {
            generated := expr;
          } else {
            generated := R.Return(Some(expr));
          }
          newEnv := env;
        }
        case EarlyReturn() => {
          generated := earlyReturn;
          readIdents := {};
          newEnv := env;
        }
        case Halt() => {
          generated := R.Identifier("panic!").Apply1(R.LiteralString("Halt", false));
          readIdents := {};
          newEnv := env;
        }
        case Print(e) => {
          var printedExpr, recOwnership, recIdents := GenExpr(e, selfIdent, env, OwnershipBorrowed);
          generated := R.Identifier("print!").Apply([R.LiteralString("{}", false), 
            R.dafny_runtime.MSel("DafnyPrintWrapper").Apply1(printedExpr)]);
          readIdents := recIdents;
          newEnv := env;
        }
      }
    }

    static const OpTable: map<BinOp, string> :=
      map[
        Mod() := "%",
        And() := "&&",
        Or() := "||",
        Div() := "/",
        Lt() := "<",
        LtChar() := "<",
        Plus() := "+",
        Minus() := "-",
        Times() := "*",
        BitwiseAnd() := "&",
        BitwiseOr() := "|",
        BitwiseXor() := "^",
        BitwiseShiftRight() := ">>",
        BitwiseShiftLeft() := "<<"
      ]

    static function NewtypeToRustType(base: Type, range: NewtypeRange)
      : Option<R.Type> {
      match range {
        case NoRange() => None
        case U8() => Some(R.Type.U8)
        case U16() => Some(R.Type.U16)
        case U32() => Some(R.Type.U32)
        case U64() => Some(R.Type.U64)
        case U128() => Some(R.Type.U128)
        case I8() => Some(R.Type.I8)
        case I16() => Some(R.Type.I16)
        case I32() => Some(R.Type.I32)
        case I64() => Some(R.Type.I64)
        case I128() => Some(R.Type.I128)
        case _ => None
      }
    }

    static method FromOwned(r: R.Expr, expectedOwnership: Ownership)
      returns (out: R.Expr, resultingOwnership: Ownership)
      ensures resultingOwnership != OwnershipAutoBorrowed
      ensures expectedOwnership != OwnershipAutoBorrowed
              ==> resultingOwnership == expectedOwnership
    {
      if expectedOwnership == OwnershipOwned || expectedOwnership == OwnershipAutoBorrowed {
        out := r;
        resultingOwnership := OwnershipOwned;
      } else if expectedOwnership == OwnershipBorrowed {
        out := R.Borrow(r);
        resultingOwnership := OwnershipBorrowed;
      } else {
        assert expectedOwnership == OwnershipBorrowedMut;
        out := R.BorrowMut(r);
        resultingOwnership := OwnershipBorrowedMut;
      }
    }

    static method FromOwnership(r: R.Expr, ownership: Ownership, expectedOwnership: Ownership)
      returns (out: R.Expr, resultingOwnership: Ownership)
      requires ownership != OwnershipAutoBorrowed
      ensures resultingOwnership != OwnershipAutoBorrowed
      ensures expectedOwnership != OwnershipAutoBorrowed
              ==> resultingOwnership == expectedOwnership
    {
      if ownership == OwnershipOwned {
        out, resultingOwnership := FromOwned(r, expectedOwnership);
        return;
      } else if ownership == OwnershipBorrowed || ownership == OwnershipBorrowedMut {
        if expectedOwnership == OwnershipOwned {
          resultingOwnership := OwnershipOwned;
          out := R.Clone(r);
        } else if expectedOwnership == ownership
                  || expectedOwnership == OwnershipAutoBorrowed {
          resultingOwnership := ownership;
          out := r;
        } else if expectedOwnership == OwnershipBorrowed
                  && ownership == OwnershipBorrowedMut {
          resultingOwnership := OwnershipBorrowed;
          out := r;
        } else {
          assert expectedOwnership == OwnershipBorrowedMut;
          resultingOwnership := OwnershipBorrowedMut;
          out := R.BorrowMut(r); // Not sure if it will ever happen
        }
      } else {
        assert false;
      }
    }

    static predicate OwnershipGuarantee(expectedOwnership: Ownership, resultingOwnership: Ownership) {
      && (expectedOwnership != OwnershipAutoBorrowed ==>
            resultingOwnership == expectedOwnership)
      && resultingOwnership != OwnershipAutoBorrowed // We know what's going on
    }

    static method GenExprLiteral(
      e: Expression,
      selfIdent: Option<string>,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Literal?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0
    {
      match e {
        case Literal(BoolLiteral(b)) => {
          r, resultingOwnership :=
            FromOwned(R.LiteralBool(b), expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(IntLiteral(i, t)) => {
          match t {
            case Primitive(Int) => {
              if |i| <= 4 {
                r := R.dafny_runtime.MSel("int!").Apply1(R.LiteralInt(i));
              } else {
                r := R.dafny_runtime.MSel("int!").Apply1(
                  R.LiteralString(i, binary := true));
              }
            }
            case o => {
              var genType := GenType(o, false, false);
              r := R.TypeAscription(R.RawExpr(i), genType);
            }
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(DecLiteral(n, d, t)) => {
          match t {
            case Primitive(Real) => {
              r := R.RcNew(R.RawExpr("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\"" + n + "\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"" + d + "\", 10).unwrap())"));
            }
            case o => {
              var genType := GenType(o, false, false);
              r := R.TypeAscription(R.RawExpr("(" + n + ".0 / " + d + ".0" + ")"), genType);
            }
          }

          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(StringLiteral(l)) => {
          r := R.dafny_runtime.MSel("string_of").Apply1(R.LiteralString(l, false));
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(CharLiteral(c)) => {
          r := R.LiteralInt(Strings.OfNat(c as nat));
          r := R.TypeAscription(r, DafnyCharUnderlying);
          r := R.dafny_runtime.MSel(DafnyChar).Apply1(r);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(Null(tpe)) => {
          // TODO: Mikael. Null will be std::ptr::null, not Option::None.
          var tpeGen := GenType(tpe, false, false);
          r := R.TypeAscription(R.RawExpr("None"), tpeGen);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
      }
    }

    static method GenExprBinary(
      e: Expression,
      selfIdent: Option<string>,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.BinOp?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0
    {
      var BinOp(op, lExpr, rExpr, format) := e;
      var becomesLeftCallsRight := match op {
        case SetMerge()
          | SetSubtraction()
          | SetIntersection()
          | SetDisjoint()
          | MapMerge()
          | MapSubtraction()
          | MultisetMerge()
          | MultisetSubtraction()
          | MultisetIntersection()
          | MultisetDisjoint()
          | Concat()
          => true
        case _ => false
      };
      var becomesRightCallsLeft := match op {
        case In() => true
        case _ => false
      };
      var becomesCallLeftRight := match op {
        case Eq(true, false) => true
        case _ => false
      };
      var expectedLeftOwnership :=
        if becomesLeftCallsRight then OwnershipAutoBorrowed
        else if becomesRightCallsLeft || becomesCallLeftRight then OwnershipBorrowed
        else OwnershipOwned;
      var expectedRightOwnership :=
        if becomesLeftCallsRight || becomesCallLeftRight then OwnershipBorrowed
        else if becomesRightCallsLeft then OwnershipAutoBorrowed
        else OwnershipOwned;
      var left, _, recIdentsL := GenExpr(lExpr, selfIdent, env, expectedLeftOwnership);
      var right, _, recIdentsR := GenExpr(rExpr, selfIdent, env, expectedRightOwnership);

      match op {
        case In() => {
          r := right.Sel("contains").Apply1(left);
        }
        case SeqProperPrefix() =>
          r := R.BinaryOp("<", left, right, format);
        case SeqPrefix() =>
          r := R.BinaryOp("<=", left, right, format);
        case SetMerge() => {
          r := left.Sel("merge").Apply1(right);
        }
        case SetSubtraction() => {
          r := left.Sel("subtract").Apply1(right);
        }
        case SetIntersection() => {
          r := left.Sel("intersect").Apply1(right);
        }
        case Subset() => {
          r := R.BinaryOp("<=", left, right, format);
        }
        case ProperSubset() => {
          r := R.BinaryOp("<", left, right, format);
        }
        case SetDisjoint() => {
          r := left.Sel("disjoint").Apply1(right);
        }
        case MapMerge() => {
          r := left.Sel("merge").Apply1(right);
        }
        case MapSubtraction() => {
          r := left.Sel("subtract").Apply1(right);
        }
        case MultisetMerge() => {
          r := left.Sel("merge").Apply1(right);
        }
        case MultisetSubtraction() => {
          r := left.Sel("subtract").Apply1(right);
        }
        case MultisetIntersection() => {
          r := left.Sel("intersect").Apply1(right);
        }
        case Submultiset() => {
          r := R.BinaryOp("<=", left, right, format);
        }
        case ProperSubmultiset() => {
          r := R.BinaryOp("<", left, right, format);
        }
        case MultisetDisjoint() => {
          r := left.Sel("disjoint").Apply1(right);
        }
        case Concat() => {
          r := left.Sel("concat").Apply1(right);
        }
        case _ => {

          if op in OpTable {
            r := R.Expr.BinaryOp(
              OpTable[op],
              left,
              right,
              format);
          } else {
            match op {
              case Eq(referential, nullable) => {
                if (referential) {
                  // TODO: Render using a call with two expressions
                  if (nullable) {
                    r := R.RawExpr("::dafny_runtime::nullable_referential_equality").Apply([left, right]);
                  } else {
                    r := R.RawExpr("::std::rc::Rc::ptr_eq").Apply([left, right]);
                  }
                } else {
                  r := R.BinaryOp("==", left, right, DAST.Format.BinOpFormat.NoFormat());
                }
              }
              case EuclidianDiv() => {
                r := R.RawExpr("::dafny_runtime::euclidian_division").Apply([left, right]);
              }
              case EuclidianMod() => {
                r := R.RawExpr("::dafny_runtime::euclidian_modulo").Apply([left, right]);
              }
              case Passthrough(op) => {
                r := R.Expr.BinaryOp(op, left, right, format);
              }
            }
          }
        }
      }
      r, resultingOwnership := FromOwned(r, expectedOwnership);
      readIdents := recIdentsL + recIdentsR;
      return;
    }

    static method GenExprConvert(
      e: Expression,
      selfIdent: Option<string>,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      if fromTpe == toTpe {
        var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
        r := recursiveGen;
        r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
        readIdents := recIdents;
      } else {
        match (fromTpe, toTpe) {
          case (Nullable(_), _) => {
            var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
            r := recursiveGen;
            if recOwned == OwnershipOwned {
              r := r.Sel("as_ref").Apply([]);
            }
            r := r.Sel("unwrap").Apply([]);
            r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
            readIdents := recIdents;
          }
          case (_, Nullable(_)) => {
            var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
            r := recursiveGen;
            if recOwned == OwnershipOwned {
              r := r.Sel("clone").Apply([]);
            }
            r := R.Call(R.Identifier("Some"), [r]);
            r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
            readIdents := recIdents;
          }
          case (_, Path(_, _, Newtype(b, range, erase, attributes))) => {
            assert {:split_here} true;
            var nativeToType := NewtypeToRustType(b, range);
            if fromTpe == b {
              var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
              readIdents := recIdents;
              match nativeToType {
                case Some(v) =>
                  r := R.dafny_runtime.MSel("truncate!").Apply([recursiveGen, R.ExprFromType(v)]);
                  r, resultingOwnership := FromOwned(r, expectedOwnership);
                case None =>
                  if erase {
                    r := recursiveGen;
                  } else {
                    var rhsType := GenType(toTpe, true, false);
                    r := R.RawExpr(rhsType.ToString(IND) + "(" + recursiveGen.ToString(IND) + ")");
                  }
                  r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
              }
            } else {
              if nativeToType.Some? {
                // Conversion between any newtypes that can be expressed as a native Rust type
                match fromTpe {
                  case Path(_, _, Newtype(b0, range0, erase0, attributes0)) => {
                    var nativeFromType := NewtypeToRustType(b0, range0);

                    if nativeFromType.Some? {
                      var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
                      r, resultingOwnership := FromOwnership(R.TypeAscription(recursiveGen, nativeToType.value), recOwned, expectedOwnership);
                      readIdents := recIdents;
                      return;
                    }
                  }
                  case _ =>
                }
                if fromTpe == Primitive(Char) {
                  var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
                  r, resultingOwnership := FromOwnership(R.TypeAscription(recursiveGen.Sel("0"), nativeToType.value), recOwned, expectedOwnership);
                  readIdents := recIdents;
                  return;
                }
              }
              assume {:axiom} Convert(Convert(expr, fromTpe, b), b, toTpe) < e; // make termination go through
              r, resultingOwnership, readIdents := GenExpr(Convert(Convert(expr, fromTpe, b), b, toTpe), selfIdent, env, expectedOwnership);
            }
          }
          case (Path(_, _, Newtype(b, range, erase, attributes)), _) => {
            var nativeFromType := NewtypeToRustType(b, range);
            if b == toTpe {
              var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
              readIdents := recIdents;
              match nativeFromType {
                case Some(v) =>
                  var toTpeRust := GenType(toTpe, false, false);
                  r := recursiveGen.Sel("into").ApplyType([toTpeRust]).Apply([]);
                  r, resultingOwnership := FromOwned(r, expectedOwnership);
                case None =>
                  if erase {
                    r := recursiveGen;
                  } else {
                    r := recursiveGen.Sel("0");
                  }
                  r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
              }
            } else {
              if nativeFromType.Some? {
                // The case where toTpe is a NewType which compiles to a native integer has already been handled.
                if toTpe == Primitive(Char) {
                  var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
                  r, resultingOwnership := FromOwnership(
                    R.dafny_runtime.MSel(DafnyChar).Apply1(
                      R.TypeAscription(recursiveGen, DafnyCharUnderlying)
                    ), recOwned, expectedOwnership);
                  readIdents := recIdents;
                  return;
                }
              }
              assume {:axiom} Convert(Convert(expr, fromTpe, b), b, toTpe) < e; // make termination go through
              r, resultingOwnership, readIdents := GenExpr(Convert(Convert(expr, fromTpe, b), b, toTpe), selfIdent, env, expectedOwnership);
            }
          }
          case (Primitive(Int), Primitive(Real)) => {
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.RcNew(R.RawExpr("::dafny_runtime::BigRational::from_integer(" + recursiveGen.ToString(IND) + ")"));
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Real), Primitive(Int)) => {
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipBorrowed);
            r := R.RawExpr("::dafny_runtime::dafny_rational_to_int(" + recursiveGen.ToString(IND) + ")");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Int), Passthrough(_)) => {
            var rhsType := GenType(toTpe, true, false);
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.RawExpr("<" + rhsType.ToString(IND) + " as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap()");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Passthrough(_), Primitive(Int)) => {
            assert {:split_here} true;
            var rhsType := GenType(fromTpe, true, false);
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.RawExpr("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from(" + recursiveGen.ToString(IND) + ")}");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Int), Primitive(Char)) => {
            var rhsType := GenType(toTpe, true, false);
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.RawExpr("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap()).unwrap()");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Char), Primitive(Int)) => {
            var rhsType := GenType(fromTpe, true, false);
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.RawExpr("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from(" + recursiveGen.ToString(IND) + " as u32)}");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Passthrough(_), Passthrough(_)) => {
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            var toTpeGen := GenType(toTpe, true, false);

            r := R.RawExpr("((" + recursiveGen.ToString(IND) + ") as " + toTpeGen.ToString(IND) + ")");

            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case _ => {
            var fromTpeGen := GenType(fromTpe, true, false);
            var toTpeGen := GenType(toTpe, true, false);
            var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
            r := R.RawExpr("(" + recursiveGen.ToString(IND) + "/* <i>Coercion from " + fromTpeGen.ToString(IND) + " to " + toTpeGen.ToString(IND) + "</i> not yet implemented */)");
            r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
            readIdents := recIdents;
          }
        }
      }
      return;
    }
    static method GenExpr(
      e: Expression,
      selfIdent: Option<string>,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 1 {
      match e {
        case Literal(_) =>
          r, resultingOwnership, readIdents :=
            GenExprLiteral(e, selfIdent, env, expectedOwnership);
        case Ident(name) => {
          var rName := escapeIdent(name);
          r := R.Identifier(rName);
          var tpe := env.GetType(rName);
          var placeboOpt := if tpe.Some? then tpe.value.ExtractMaybePlacebo() else None;
          var currentlyBorrowed := env.IsBorrowed(name); // Otherwise names are owned 
          var noNeedOfClone := env.HasCopySemantics(name);
          if placeboOpt.Some? {
            r := r.Sel("read").Apply([]);
            currentlyBorrowed := false;
            noNeedOfClone := true; // No need to clone it, it's already owned
          }
          if expectedOwnership == OwnershipAutoBorrowed {
            resultingOwnership := OwnershipOwned;
            // No need to do anything
          } else if expectedOwnership == OwnershipBorrowedMut {
            if tpe.Some? && (tpe.value.PointerMut? || tpe.value.Pointer?) {
              r := R.dafny_runtime.MSel("modify!").Apply1(r);
            } else {
              r := R.BorrowMut(r); // Needs to be explicit for out-parameters on methods
            }
            resultingOwnership := OwnershipBorrowedMut;
          } else if expectedOwnership == OwnershipOwned {
            if !noNeedOfClone {
              print "Cloning id " + name + " to:\n"; 
              print "Environment: ", env, "\n";
              r := R.Clone(r); // We don't transfer the ownership of an identifier
            }
            resultingOwnership := OwnershipOwned;
          } else if currentlyBorrowed {
            assert expectedOwnership == OwnershipBorrowed;
            resultingOwnership := OwnershipBorrowed;
          } else {
            // It's currently owned. If it's a pointer, we need to convert it to a borrow
            if tpe.Some? && (tpe.value.PointerMut? || tpe.value.Pointer?) {
              r := R.dafny_runtime.MSel("read!").Apply1(r);
            } else {
              r := R.Borrow(r); // Needs to be explicit for out-parameters on methods
            }
            resultingOwnership := OwnershipBorrowed;
          }
          readIdents := {name};
          return;
        }
        case Companion(path) => {
          r := GenPathExpr(path);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case InitializationValue(typ) => {
          var typExpr := GenType(typ, false, false);
          print "Getting initialization value for ", typ, ":";
          if typExpr.PointerMut? {
            r := R.std.MSel("ptr").MSel("null_mut").Apply([]);
          } else {
            r := R.RawExpr("<" + typExpr.ToString(IND) + " as std::default::Default>::default()");
          }
          print r, "\n";
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Tuple(values) => {
          var s := "(";
          readIdents := {};

          var i := 0;
          while i < |values| {
            if i > 0 {
              s := s + " ";
            }

            var recursiveGen, _, recIdents := GenExpr(values[i], selfIdent, env, OwnershipOwned);

            s := s + recursiveGen.ToString(IND) + ",";
            readIdents := readIdents + recIdents;

            i := i + 1;
          }
          s := s + ")";
          r := R.RawExpr(s);

          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case New(path, typeArgs, args) => {
          // args are provided if it is an extern type
          r := GenPathExpr(path);
          if |typeArgs| > 0 {
            var typeExprs := [];
            for i := 0 to |typeArgs| {
              var typeExpr := GenType(typeArgs[i], false, false);
              typeExprs := typeExprs + [typeExpr];
            }
            r := r.ApplyType(typeExprs);
          }
          r := r.MSel("_allocated");

          readIdents := {};
          var arguments := [];
          for i := 0 to |args| {
            var recursiveGen, _, recIdents := GenExpr(args[i], selfIdent, env, OwnershipOwned);
            arguments := arguments + [recursiveGen];
            readIdents := readIdents + recIdents;
          }
          r := r.Apply(arguments);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case NewArray(dims, typ) => {
          var i := |dims| - 1;
          var genTyp := GenType(typ, false, false);
          // TODO (Mikael): Prevent arrays from being initialized without initialization code
          var s := "<" + genTyp.ToString(IND) + " as ::std::default::Default>::default()";
          readIdents := {};
          while i >= 0 {
            var recursiveGen, _, recIdents := GenExpr(dims[i], selfIdent, env, OwnershipOwned);

            s := "::std::rc::Rc::new(::std::cell::RefCell::new(vec![" + s + "; <usize as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap()]))";
            readIdents := readIdents + recIdents;

            i := i - 1;
          }

          r := R.RawExpr(s);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case DatatypeValue(datatypeType, typeArgs, variant, isCo, values) => {
          r := GenPathExpr(datatypeType.path);
          var genTypeArgs := [];
          for i := 0 to |typeArgs| {
            var typeExpr := GenType(typeArgs[i], false, false);
            genTypeArgs := genTypeArgs + [typeExpr];
          }
          if |typeArgs| > 0 {
            r := r.ApplyType(genTypeArgs);
          }
          r := r.MSel(escapeIdent(variant));
          readIdents := {};

          var assignments: seq<R.AssignIdentifier> := [];
          for i := 0 to |values| {
            var (name, value) := values[i];

            if isCo {
              var recursiveGen, _, recIdents := GenExpr(value, selfIdent, Environment.Empty(), OwnershipOwned);

              readIdents := readIdents + recIdents;
              var allReadCloned := "";
              while recIdents != {} decreases recIdents {
                var next: string :| next in recIdents;
                allReadCloned := allReadCloned + "let " + escapeIdent(next) + " = " + escapeIdent(next) + ".clone();\n";
                recIdents := recIdents - {next};
              }
              var assigned: string := "::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n" + allReadCloned + "move || (" + recursiveGen.ToString(IND) + ")})))";
              assignments := assignments + [R.AssignIdentifier(escapeIdent(name), R.RawExpr(assigned))];
            } else {
              var recursiveGen, _, recIdents := GenExpr(value, selfIdent, env, OwnershipOwned);

              assignments := assignments + [R.AssignIdentifier(escapeIdent(name), recursiveGen)];
              readIdents := readIdents + recIdents;
            }
          }
          r := R.StructBuild(r, assignments);
          if IsRcWrapped(datatypeType.attributes) {
            r := R.RcNew(r);
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case Convert(_, _, _) => {
          r, resultingOwnership, readIdents :=
            GenExprConvert(e, selfIdent, env, expectedOwnership);
        }
        case SeqConstruct(length, expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
          var lengthGen, _, lengthIdents := GenExpr(length, selfIdent, env, OwnershipOwned);

          r := R.RawExpr("{\nlet _initializer = " + recursiveGen.ToString(IND) + ";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), " + lengthGen.ToString(IND) + ").map(|i| _initializer.0(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}");

          readIdents := recIdents + lengthIdents;
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SeqValue(exprs, typ) => {
          readIdents := {};

          var genTpe := GenType(typ, false, false);

          var i := 0;
          var args := [];
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, env, OwnershipOwned);
            readIdents := readIdents + recIdents;
            args := args + [recursiveGen];

            i := i + 1;
          }
          r := R.dafny_runtime.MSel("seq!").Apply(args);
          if |args| == 0 {
            r := R.TypeAscription(r,
                                  R.dafny_runtime_type.MSel("Sequence").Apply1(genTpe));
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SetValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, env, OwnershipOwned);

            generatedValues := generatedValues + [recursiveGen];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }
          r := R.dafny_runtime.MSel("set!").Apply(generatedValues);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MultisetValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, env, OwnershipOwned);

            generatedValues := generatedValues + [recursiveGen];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }
          r := R.dafny_runtime.MSel("multiset!").Apply(generatedValues);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case ToMultiset(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          r := recursiveGen.Sel("as_dafny_multiset").Apply([]);
          readIdents := recIdents;
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MapValue(mapElems) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |mapElems| {
            var recursiveGenKey, _, recIdentsKey := GenExpr(mapElems[i].0, selfIdent, env, OwnershipOwned);
            var recursiveGenValue, _, recIdentsValue := GenExpr(mapElems[i].1, selfIdent, env, OwnershipOwned);

            generatedValues := generatedValues + [(recursiveGenKey, recursiveGenValue)];
            readIdents := readIdents + recIdentsKey + recIdentsValue;
            i := i + 1;
          }

          i := 0;
          var arguments := [];
          while i < |generatedValues| {
            var genKey := generatedValues[i].0;
            var genValue := generatedValues[i].1;

            arguments := arguments + [R.BinaryOp("=>", genKey, genValue, DAST.Format.BinOpFormat.NoFormat())];
            i := i + 1;
          }
          r := R.dafny_runtime.MSel("map!").Apply(arguments);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SeqUpdate(expr, index, value) => {
          var exprR, _, exprIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          var indexR, indexOwnership, indexIdents := GenExpr(index, selfIdent, env, OwnershipBorrowed);
          var valueR, valueOwnership, valueIdents := GenExpr(value, selfIdent, env, OwnershipBorrowed);
          r := exprR.Sel("update_index").Apply([indexR, valueR]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := exprIdents + indexIdents + valueIdents;
          return;
        }
        case MapUpdate(expr, index, value) => {
          var exprR, _, exprIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          var indexR, indexOwnership, indexIdents := GenExpr(index, selfIdent, env, OwnershipBorrowed);
          var valueR, valueOwnership, valueIdents := GenExpr(value, selfIdent, env, OwnershipBorrowed);
          r := exprR.Sel("update_index").Apply([indexR, valueR]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := exprIdents + indexIdents + valueIdents;
          return;
        }
        case This() => {
          match selfIdent {
            case Some(id) => {
              r := R.Identifier(id);
              if expectedOwnership == OwnershipOwned {
                r := R.Clone(r);
                resultingOwnership := OwnershipOwned;
              } else if expectedOwnership == OwnershipBorrowed || expectedOwnership == OwnershipAutoBorrowed {
                if id != "self" {
                  r := R.Borrow(r);
                }
                resultingOwnership := OwnershipBorrowed;
              } else {
                assert expectedOwnership == OwnershipBorrowedMut;
                if id != "self" {
                  r := R.BorrowMut(r);
                }
                resultingOwnership := OwnershipBorrowedMut;
              }

              readIdents := {id};
            }
            case None => {
              r := R.RawExpr("panic!(\"this outside of a method\")");
              r, resultingOwnership := FromOwned(r, expectedOwnership);
              readIdents := {};
            }
          }
          return;
        }
        case Ite(cond, t, f) => {
          assert {:split_here} true;
          var cond, _, recIdentsCond := GenExpr(cond, selfIdent, env, OwnershipOwned);
          var condString := cond.ToString(IND);

          var _, tHasToBeOwned, _ := GenExpr(t, selfIdent, env, expectedOwnership); // check if t has to be owned even if not requested
          var fExpr, fOwned, recIdentsF := GenExpr(f, selfIdent, env, tHasToBeOwned);
          var fString := fExpr.ToString(IND);
          var tExpr, _, recIdentsT := GenExpr(t, selfIdent, env, fOwned); // there's a chance that f forced ownership
          var tString := tExpr.ToString(IND);

          r := R.RawExpr("(if " + condString + " {\n" + tString + "\n} else {\n" + fString + "\n})");

          r, resultingOwnership := FromOwnership(r, fOwned, expectedOwnership);
          readIdents := recIdentsCond + recIdentsT + recIdentsF;
          return;
        }
        case UnOp(Not, e, format) => {
          var recursiveGen, _, recIdents := GenExpr(e, selfIdent, env, OwnershipOwned);

          r := R.UnaryOp("!", recursiveGen, format);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case UnOp(BitwiseNot, e, format) => {
          var recursiveGen, _, recIdents := GenExpr(e, selfIdent, env, OwnershipOwned);

          r := R.UnaryOp("~", recursiveGen, format);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case UnOp(Cardinality, e, format) => {
          var recursiveGen, recOwned, recIdents := GenExpr(e, selfIdent, env, OwnershipAutoBorrowed);

          r := recursiveGen.Sel("cardinality").Apply([]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case BinOp(_, _, _, _) =>
          r, resultingOwnership, readIdents :=
            GenExprBinary(e, selfIdent, env, expectedOwnership);
        case ArrayLen(expr, dim) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);

          if dim == 0 {
            r := R.RawExpr("::dafny_runtime::BigInt::from((" + recursiveGen.ToString(IND) + ").borrow().len())");
          } else {
            var s := R.RawExpr("::dafny_runtime::BigInt::from(m.borrow().len())").ToString(IND);
            var i := 1;
            while i < dim {
              s := "m.borrow().get(0).map(|m| " + s + ").unwrap_or(::dafny_runtime::BigInt::from(0))";
              i := i + 1;
            }

            r := R.RcNew(R.RawExpr("(" + recursiveGen.ToString(IND) + ")" + ".borrow().get(0).map(|m| " + s + ").unwrap_or(::dafny_runtime::BigInt::from(0))"));
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case MapKeys(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
          readIdents := recIdents;
          r := recursiveGen.Sel("keys").Apply([]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MapValues(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
          readIdents := recIdents;
          r := recursiveGen.Sel("values").Apply([]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SelectFn(on, field, isDatatype, isStatic, arity) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
          var s: string;
          var onString := onExpr.ToString(IND);

          if isStatic {
            s := onString + "::" + escapeIdent(field);
          } else {
            s := "{\n";
            s := s + "let callTarget = (" + onString + (if onOwned == OwnershipOwned then ")" else ").clone()") + ";\n";
            var args := "";
            var i := 0;
            while i < arity {
              if i > 0 {
                args := args + ", ";
              }
              args := args + "arg" + Strings.OfNat(i);
              i := i + 1;
            }
            s := s + "move |" + args + "| {\n";
            s := s + "callTarget." + field + "(" + args + ")\n";
            s := s + "}\n";
            s := s + "}";
          }

          var typeShape := "dyn ::std::ops::Fn(";
          var i := 0;
          while i < arity {
            if i > 0 {
              typeShape := typeShape + ", ";
            }
            typeShape := typeShape + "&_";
            i := i + 1;
          }

          typeShape := typeShape + ") -> _";

          s := "::dafny_runtime::FunctionWrapper(::std::rc::Rc::new(" + s + ") as ::std::rc::Rc<" + typeShape + ">)";
          r := R.RawExpr(s);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case Select(Companion(c), field, isConstant, isDatatype, fieldType) => {
          var onExpr, onOwned, recIdents := GenExpr(Companion(c), selfIdent, env, OwnershipBorrowed);

          r := onExpr.MSel(escapeIdent(field)).Apply([]);

          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case Select(on, field, isConstant, isDatatype, fieldType) => {
          if isDatatype || isConstant {
            var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
            r := onExpr.Sel(escapeIdent(field)).Apply([]);
            var typ := GenType(fieldType, false, false);
            if typ.HasCopySemantics() &&
               (expectedOwnership == OwnershipOwned ||  expectedOwnership == OwnershipAutoBorrowed) {
              resultingOwnership := OwnershipOwned;
            } else {
              r, resultingOwnership := FromOwnership(r, OwnershipBorrowed, expectedOwnership);
            }
            readIdents := recIdents;
          } else {
            var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
            r := onExpr;
            if onExpr != R.self {// self are already borrowed
              match onExpr { // Special case, the constructor.
                case UnaryOp("&", Identifier("this"), _) =>
                  r := R.Identifier("this");
                case _ =>
              }
              print "Selection of not self: ", on, "\n", onExpr, "\nonOwned = ", onOwned, "\n";
              r := R.dafny_runtime.MSel("read!").Apply1(r);
            }
            r := r.Sel(escapeIdent(field));
            r, resultingOwnership := FromOwnership(r, OwnershipBorrowed, expectedOwnership);
            readIdents := recIdents;
          }
          return;
        }
        case Index(on, collKind, indices) => {
          assert {:split_here} true;
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
          readIdents := recIdents;
          r := onExpr;

          var i := 0;
          while i < |indices| {
            if collKind == CollKind.Array {
              r := r.Sel("borrow").Apply([]);
            }
            var idx, idxOwned, recIdentsIdx := GenExpr(indices[i], selfIdent, env, OwnershipBorrowed);
            r := r.Sel("get").Apply1(idx);
            readIdents := readIdents + recIdentsIdx;
            i := i + 1;
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case IndexRange(on, isArray, low, high) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
          readIdents := recIdents;

          var methodName := if low.Some? then
            if high.Some? then "slice" else "drop"
          else if high.Some? then "take" else "";

          var arguments := [];
          match low {
            case Some(l) => {
              var lExpr, _, recIdentsL := GenExpr(l, selfIdent, env, OwnershipBorrowed);
              arguments := arguments + [lExpr];
              readIdents := readIdents + recIdentsL;
            }
            case None => {}
          }

          match high {
            case Some(h) => {
              var hExpr, _, recIdentsH := GenExpr(h, selfIdent, env, OwnershipBorrowed);
              arguments := arguments + [hExpr];
              readIdents := readIdents + recIdentsH;
            }
            case None => {}
          }

          r := onExpr;
          if isArray {
            if methodName != "" {
              methodName := "_" + methodName;
            }
            r := R.dafny_runtime_Sequence.MSel("from_array"+methodName).Apply(arguments);
          } else {
            if methodName != "" {
              r := r.Sel(methodName).Apply(arguments);
            }
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case TupleSelect(on, idx, fieldType) => {
          var onExpr, onOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
          r := onExpr.Sel(Strings.OfNat(idx));
          r, resultingOwnership := FromOwnership(r, onOwnership, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case Call(on, name, typeArgs, args) => {
          readIdents := {};

          var onExpr, _, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);

          var typeExprs := [];
          if (|typeArgs| >= 1) {
            for typeI := 0 to |typeArgs| {
              var typeExpr := GenType(typeArgs[typeI], false, false);
              typeExprs := typeExprs + [typeExpr];
            }
          }

          var argExprs := [];
          for i := 0 to |args| {
            var argOwnership := OwnershipBorrowed;
            if name.Name? && i < |name.signature.parameters| {
              var tpe := GenType(name.signature.parameters[i].typ, false, false);
              if tpe.HasCopySemantics() {
                argOwnership := OwnershipOwned;
              }
            }

            var argExpr, _, argIdents := GenExpr(args[i], selfIdent, env, argOwnership);
            argExprs := argExprs + [argExpr];
            readIdents := readIdents + argIdents;
          }

          readIdents := readIdents + recIdents;
          var renderedName := match name {
            case Name(ident, _, _) => escapeIdent(ident)
            case MapBuilderAdd | SetBuilderAdd => "add"
            case MapBuilderBuild | SetBuilderBuild => "build"
          };
          // Pointers in the role of "self" must be converted to borrowed versions.
          match on {
            case Companion(_) => {
              onExpr := onExpr.MSel(renderedName);
            }
            case _ => {
              if onExpr != R.self {
                match name {
                  case Name(_, Some(tpe), _) =>
                    var typ := GenType(tpe, false, false);
                    if typ.Pointer? || typ.PointerMut? {
                      onExpr := R.dafny_runtime.MSel("read!").Apply1(onExpr);
                    }
                  case _ =>
                }
              }
              onExpr := onExpr.Sel(renderedName);
            }
          }
          r := onExpr;
          if |typeExprs| > 0 {
            r := r.ApplyType(typeExprs);
          }
          r := r.Apply(argExprs);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case Lambda(paramsDafny, retType, body) => {
          var params := GenParams(paramsDafny);
          var paramNames := [];
          var paramTypesMap := map[];
          for i := 0 to |params| {
            var name := params[i].name;
            paramNames := paramNames + [name];
            paramTypesMap := paramTypesMap[name := params[i].tpe];
          }
          var env := Environment(paramNames, paramTypesMap);

          var recursiveGen, recIdents, _ := GenStmts(body, if selfIdent != None then Some("_this") else None, env, true, R.RawExpr(""));
          readIdents := {};
          var allReadCloned := "";
          while recIdents != {} decreases recIdents {
            var next: string :| next in recIdents;

            if selfIdent != None && next == "_this" {
              if selfIdent != None {
                allReadCloned := allReadCloned + "let _this = self.clone();\n";
              }
            } else if !(next in paramNames) {
              allReadCloned := allReadCloned + "let " + escapeIdent(next) + " = " + escapeIdent(next) + ".clone();\n";
              readIdents := readIdents + {next};
            }

            recIdents := recIdents - {next};
          }

          var paramsString := "";
          var paramTypes := "";
          for i := 0 to |params| {
            if i > 0 {
              paramsString := paramsString + ", ";
              paramTypes := paramTypes + ", ";
            }
            paramsString := paramsString + escapeIdent(params[i].name) + ": " + R.Borrowed(params[i].tpe).ToString(IND);
            paramTypes := paramTypes + R.Borrowed(params[i].tpe).ToString(IND);
          }

          var retTypeGen := GenType(retType, false, true);

          r := R.RawExpr("::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn ::std::ops::Fn(" + paramTypes + ") -> " + retTypeGen.ToString(IND) + ">>({\n" + allReadCloned + "::std::rc::Rc::new(move |" + paramsString + "| -> " + retTypeGen.ToString(IND) + " {\n" + recursiveGen.ToString(IND) + "\n})})");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case BetaRedex(values, retType, expr) => {
          var paramNames := [];
          var paramFormals := GenParams(Std.Collections.Seq.Map(
            (value: (Formal, Expression)) => value.0, values));
          var paramTypes := map[];
          var paramNamesSet := {};
          for i := 0 to |values| {
            var name := values[i].0.name;
            var rName := escapeIdent(name);
            paramNames := paramNames + [rName];
            paramTypes := paramTypes[rName := paramFormals[i].tpe];
            paramNamesSet := paramNamesSet + {name};
          }

          readIdents := {};
          var s := "{\n";

          var paramsString := "";
          for i := 0 to |values| {
            if i > 0 {
              paramsString := paramsString + ", ";
            }

            var typStr := GenType(values[i].0.typ, false, true);

            var valueGen, _, recIdents := GenExpr(values[i].1, selfIdent, env, OwnershipOwned);
            s := s + "let " + escapeIdent(values[i].0.name) + ": " + typStr.ToString(IND) + " = ";
            readIdents := readIdents + recIdents;

            s := s + valueGen.ToString(IND) + ";\n";
          }

          var newEnv := Environment(paramNames, paramTypes);

          var recGen, recOwned, recIdents := GenExpr(expr, selfIdent, newEnv, expectedOwnership);
          readIdents := recIdents - paramNamesSet;

          s := s  + recGen.ToString(IND) + "\n}";
          r := R.RawExpr(s);
          r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
          return;
        }
        case IIFE(name, tpe, value, iifeBody) => {
          var valueGen, _, recIdents := GenExpr(value, selfIdent, env, OwnershipOwned);

          readIdents := recIdents;
          var valueTypeGen := GenType(tpe, false, true);
          var bodyGen, _, bodyIdents := GenExpr(iifeBody, selfIdent, env, OwnershipOwned);
          readIdents := readIdents + (bodyIdents - {name.id});

          r := R.RawExpr("{\nlet " + escapeIdent(name.id) + ": " + valueTypeGen.ToString(IND) + " = " + valueGen.ToString(IND) + ";\n" + bodyGen.ToString(IND) + "\n}");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case Apply(func, args) => {
          var funcExpr, _, recIdents := GenExpr(func, selfIdent, env, OwnershipBorrowed);
          readIdents := recIdents;

          var argString := "";
          var i := 0;
          while i < |args| {
            if i > 0 {
              argString := argString + ", ";
            }

            var argExpr, argOwned, argIdents := GenExpr(args[i], selfIdent, env, OwnershipBorrowed);
            var argExprString := argExpr.ToString(IND);
            if argOwned == OwnershipOwned {
              argExprString := "&" + argExprString;
            }

            argString := argString + argExprString;
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          r := R.RawExpr("((" + funcExpr.ToString(IND) + ").0" + "(" + argString + "))");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case TypeTest(on, dType, variant) => {
          var exprGen, _, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
          var dTypePath := GenPath(dType);
          r := R.Identifier("matches!").Apply([exprGen.Sel("as_ref").Apply([]), R.RawExpr(dTypePath.MSel(escapeIdent(variant)).ToString(IND) + "{ .. }")]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case BoolBoundedPool() => {
          r := R.RawExpr("[false, true]");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case SetBoundedPool(of) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, env, OwnershipBorrowed);
          r := R.RawExpr("(" + exprGen.ToString(IND) + ").iter()");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case SeqBoundedPool(of, includeDuplicates) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, env, OwnershipBorrowed);
          var s := "(" + exprGen.ToString(IND) + ").iter()";
          if !includeDuplicates {
            s := "::dafny_runtime::itertools::Itertools::unique(" + s + ")";
          }
          r := R.RawExpr(s);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case IntRange(lo, hi) => {
          var lo, _, recIdentsLo := GenExpr(lo, selfIdent, env, OwnershipOwned);
          var hi, _, recIdentsHi := GenExpr(hi, selfIdent, env, OwnershipOwned);

          r := R.RawExpr("::dafny_runtime::integer_range(" + lo.ToString(IND) + ", " + hi.ToString(IND) + ")");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdentsLo + recIdentsHi;
          return;
        }
        case MapBuilder(keyType, valueType) => {
          var kType := GenType(keyType, false, false);
          var vType := GenType(valueType, false, false);
          r := R.RawExpr("::dafny_runtime::MapBuilder::<" + kType.ToString(IND) + ", " + vType.ToString(IND) + ">::new()");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case SetBuilder(elemType) => {
          var eType := GenType(elemType, false, false);
          readIdents := {};
          r := R.RawExpr("::dafny_runtime::SetBuilder::<" + eType.ToString(IND) + ">::new()");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
      }
    }

    static method Compile(p: seq<Module>) returns (s: string) {
      s := "#![allow(warnings, unconditional_panic)]\n";
      s := s + "#![allow(nonstandard_style)]\n";
      s := s + "extern crate dafny_runtime;\n";

      var i := 0;
      while i < |p| {
        var generated: string;
        var m := GenModule(p[i], []);
        generated := m.ToString("");

        if i > 0 {
          s := s + "\n";
        }

        s := s + generated;
        i := i + 1;
      }
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "\nfn main() {\n";
      var i := 0;
      while i < |fullName| {
        if i > 0 {
          s := s + "::";
        }
        s := s + escapeIdent(fullName[i]);
        i := i + 1;
      }
      s := s + "();\n}";
    }
  }
}

module {:extern "DCOMP"} DafnyToRustCompiler refines DafnyToRustCompilerAbstract {
  const UnicodeChars := true
}
module {:extern "DCOMPUTF16"} DafnyToRustCompilerUTF16 refines DafnyToRustCompilerAbstract {
  const UnicodeChars := false
}

