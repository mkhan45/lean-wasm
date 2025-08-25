import Wasm.Compiler
import Wasm.Ast

inductive TStack : StackTypes -> Type
| nil : TStack []
| cons (t : TVal t') (ts : TStack ts') : TStack (t' :: ts')

infixr:50 " :: " => TStack.cons

def evalOpT (op : Op inpTys outTys) (inp : TStack inpTys) : TStack outTys := match op, inp with
  | .I32Const n, inp => .I32 n :: inp
  | .F32Const n, inp => .F32 n :: inp
  | .I32Add, .I32 a :: .I32 b :: xs => .I32 (b + a) :: xs
  | .I32Sub, .I32 a :: .I32 b :: xs => .I32 (b - a) :: xs
  | .F32Add, .F32 a :: .F32 b :: xs => .F32 (b + a) :: xs

def evalProgT (prog : Prog inpTys outTys) (st : TStack inpTys) : TStack outTys := match prog with
| .nil => st
| .cons op rest => evalProgT rest (evalOpT op st)

def Expr.evalT (e : Expr T) : TVal T := match e with
| .I32Lit n => .I32 n
| .F32Lit n => .F32 n
| .I32Add lhs rhs => .I32 $ lhs.evalT.toRepr + rhs.evalT.toRepr
| .I32Sub lhs rhs => .I32 $ lhs.evalT.toRepr - rhs.evalT.toRepr
| .F32Add lhs rhs => .F32 $ lhs.evalT.toRepr + rhs.evalT.toRepr

theorem prog_eval_concat_t : evalProgT (Prog.concat l r) st = evalProgT r (evalProgT l st) := by
  induction l with
  | nil => simp; conv => rhs; arg 2; unfold evalProgT;
  | cons op rest ih => conv => left; unfold Prog.concat; unfold evalProgT;
                       conv => right; arg 2; unfold evalProgT;
                       rw [ih];

theorem prog_eval_append_t : evalProgT (Prog.append l op) st = evalOpT op (evalProgT l st) := by
  induction l with
  | nil => simp; rfl;
  | cons op rest ihr => simp [evalProgT]; rw [ihr];

theorem compile_eq_evalT {st : TStack ts} : ∀ (e : Expr T), evalProgT e.compile st = TStack.cons e.evalT st := by
  intro e;
  induction e generalizing st ts with
  | I32Lit n => simp [Expr.evalT, Expr.compile, evalProgT, evalOpT];
  | F32Lit n => simp [Expr.evalT, Expr.compile, evalProgT, evalOpT];
  | I32Add lhs rhs ihl ihr =>
      simp [Expr.evalT, Expr.compile];
      rw [prog_append_assoc, prog_eval_concat_t, prog_eval_append_t];
      rw [ihl, ihr];
      let .I32 a := rhs.evalT
      let .I32 b := lhs.evalT
      unfold evalOpT; simp;
  | I32Sub lhs rhs ihl ihr =>
      simp [Expr.evalT, Expr.compile];
      rw [prog_append_assoc, prog_eval_concat_t, prog_eval_append_t];
      rw [ihl, ihr];
      let .I32 a := rhs.evalT
      let .I32 b := lhs.evalT
      unfold evalOpT; simp;
  | F32Add lhs rhs ihl ihr =>
      simp [Expr.evalT, Expr.compile];
      rw [prog_append_assoc, prog_eval_concat_t, prog_eval_append_t];
      rw [ihl, ihr];
      let .F32 a := rhs.evalT
      let .F32 b := lhs.evalT
      unfold evalOpT; simp;
