import Test.my_utils
import chorlean.Network
import Lean

open Lean Elab Meta

inductive locVal (a:Type) (s:String) where
| Wrap: a -> locVal a s
| Empty: locVal a s

def locVar := String -> String

inductive Sorts
| NatS  : Sorts
| BoolS : Sorts
| StringS: Sorts

inductive Lit: Sorts -> Type
| NatL  : Nat  → Lit .NatS
| BoolL : Bool → Lit .BoolS
| StringL: String -> Lit .StringS

inductive UnOp: Sorts -> Sorts -> Type
| Not  : UnOp .BoolS .BoolS

inductive BinOp: Sorts -> Sorts -> Sorts -> Type
| Concat  : BinOp .StringS .StringS .StringS
| Add     : BinOp .NatS .NatS .NatS
| Less    : BinOp .NatS .NatS .BoolS
| And     : BinOp .BoolS .BoolS .BoolS

inductive Exp: Sorts -> Type
| Lit : Lit a → Exp a
| Var : String → Exp a
| Un  : UnOp a b → Exp a → Exp b
| Bin : BinOp a b c → Exp a → Exp b → Exp c

inductive Glob
| Comp   : String -> String → Exp a → Glob -> Glob
| If     : Exp .BoolS → Glob → Glob → Glob
| Comm   : String -> String -> String -> Glob -> Glob
| Return : Exp a -> Glob

inductive MultiProg
| Noop   : MultiProg -> MultiProg
| Local  : String -> List String → Exp a → MultiProg -> MultiProg
| If     : Exp .BoolS → MultiProg → MultiProg → MultiProg
| Return : Exp a -> MultiProg
--| Comm   : String -> String -> String -> MultiProg


def Exp.vars: Exp a -> List String
| Lit _ => []
| Var v => [v]
| Un _ e => e.vars
| Bin _ e1 e2 => e1.vars ++ e2.vars

def Sorts.toLean: Sorts -> String
| StringS => "String"
| NatS => "Nat"
| BoolS => "Bool"

def Lit.toLean: Lit a -> String
| NatL n => toString n
| BoolL b => toString b
| StringL s => s

def BinOp.toLean: BinOp _a _b _c -> String
| Concat => "++"
| Add    => "+"
| Less   => "<"
| And    => "&&"

def UnOp.toLean: UnOp _a _b -> String
| Not => "!"


def Exp.toLean: Exp a -> String
| Lit l   => l.toLean
| Var s   => s
| Un op e => s!"({op.toLean} {e.toLean})"
| Bin op e1 e2 => s!"({e1.toLean} {op.toLean} {e2.toLean})"

def Glob.toLean: Glob -> String
| Comp v loc e next   => s!"{v}@{loc} := {e.toLean}\n{next.toLean}"
| If cond p1 p2       => s!"if {cond.toLean} then\n {p1.toLean}\nelse\n {p2.toLean}"
| Comm s r v next     => s!"{s} ~ {v} ~> {r}\n{next.toLean}"
| Return e            => s!"return {e.toLean}"
-- | Local loc cs e next => s!"on {loc} capture {cs} and do {e.toLean}\n{next.toLean}"
-- | If  cond p1 p2 => s!"if {cond.toLean} then\n {p1.toLean}\nelse\n {p2.toLean}"
-- | Return e => s!"return {e.toLean}"
-- | Return e => s!"return {e.toLean}"

#check Lit.StringL "as"

def test_expr: Exp .StringS := .Bin .Concat (.Lit (.StringL "hello")) (.Lit (.StringL "world"))

def test_expr2: Exp .StringS := .Bin .Concat (.Lit (.StringL "hello")) (.Var "var")


def testprog : Glob := .Comp "value" "client" test_expr (.Return test_expr)

#eval toString (testprog.toLean)
#eval test_expr2.vars

declare_syntax_cat multi_lit
syntax num       : multi_lit
syntax str       : multi_lit
syntax "true"    : multi_lit
syntax "false"   : multi_lit

def elabMultiLit : Syntax → MetaM Expr
  -- `mkAppM` creates an `Expr.app`, given the function `Name` and the args
  -- `mkNatLit` creates an `Expr` from a `Nat`
  | `(multi_lit| $n:num) => mkAppM ``MultiLit.Nat  #[mkNatLit n.getNat]
  | `(multi_lit| $s:str) => mkAppM ``MultiLit.String  #[mkStrLit s.getString]
  | `(multi_lit| true  ) => mkAppM ``MultiLit.Bool #[.const ``Bool.true []]
  | `(multi_lit| false ) => mkAppM ``MultiLit.Bool #[.const ``Bool.false []]
  | _ => throwUnsupportedSyntax


elab "test_elabIMPLit " l:multi_lit : term => elabMultiLit l

#reduce test_elabIMPLit 4     -- IMPLit.NatS 4
#reduce test_elabIMPLit true  -- IMPLit.BoolS true
#reduce test_elabIMPLit "false" -- IMPLit.BoolS true
#check test_elabIMPLit "false"


declare_syntax_cat multi_binop
syntax "+"       : multi_binop
syntax "and"     : multi_binop
syntax "++"       : multi_binop
syntax "<"       : multi_binop


def elabMultiBinOp : Syntax → MetaM Expr
  | `(multi_binop| +)   => return .const ``MultiBinOp.Add []
  | `(multi_binop| and) => return .const ``MultiBinOp.And []
  | `(multi_binop| <)   => return .const ``MultiBinOp.Less []
  | `(multi_binop| ++)   => return .const ``MultiBinOp.Concat []
  | _ => throwUnsupportedSyntax

declare_syntax_cat                   multi_expr
syntax multi_lit                          : multi_expr
syntax ident                              : multi_expr
syntax multi_expr multi_binop multi_expr  : multi_expr
syntax "(" multi_expr ")"                 : multi_expr

partial def elabMultiExpr : Syntax → MetaM Expr
  | `(multi_expr| $l:multi_lit) => do
    let l ← elabMultiLit l
    mkAppM ``MultiExpr.Lit #[l]
  -- `mkStrLit` creates an `Expr` from a `String`
  | `(multi_expr| $i:ident) => mkAppM ``MultiExpr.Var #[mkStrLit i.getId.toString]
  | `(multi_expr| $l:multi_expr $b:multi_binop $r:multi_expr) => do
    let l ← elabMultiExpr l -- recurse!
    let r ← elabMultiExpr r -- recurse!
    let b ← elabMultiBinOp b
    mkAppM ``MultiExpr.Bin #[b, l, r]
  | `(multi_expr| ($e:multi_expr)) => elabMultiExpr e
  | _ => throwUnsupportedSyntax


elab "test_elabIMPExpr " e:multi_expr : term => elabMultiExpr e

#check test_elabIMPExpr a
-- IMPExpr.var "a"

#reduce test_elabIMPExpr a + 5
-- IMPExpr.bin IMPBinOp.add (IMPExpr.var "a") (IMPExpr.lit (IMPLit.NatS 5))

#reduce test_elabIMPExpr 1 + true
-- IMPExpr.bin IMPBinOp.add (IMPExpr.lit (IMPLit.NatS 1)) (IMPExpr.lit (IMPLit.BoolS true))
