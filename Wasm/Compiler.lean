import Wasm

inductive Expr : ValType -> Type
| I32Lit (n : UInt32) : Expr .I32
| F32Lit (n : Float) : Expr .F32
| I32Add (lhs : Expr .I32) (rhs : Expr .I32) : Expr .I32
| I32Sub (lhs : Expr .I32) (rhs : Expr .I32) : Expr .I32
| F32Add (lhs : Expr .F32) (rhs : Expr .F32) : Expr .F32

theorem val_repr (v : { v : Val // v.toValType = T}) : v.val.toValType.repr = T.repr := by rw [v.property];

def Expr.eval (e : Expr T) : { v : Val // v.toValType = T } := match e with
| .I32Lit n => ⟨.I32 n, rfl⟩
| .F32Lit n => ⟨.F32 n, rfl⟩
| .I32Add lhs rhs => ⟨.I32 $ Val.toReprR lhs.eval + Val.toReprR rhs.eval, rfl⟩
| .I32Sub lhs rhs => ⟨.I32 $ Val.toReprR lhs.eval - Val.toReprR rhs.eval, rfl⟩
| .F32Add lhs rhs => ⟨.F32 $ Val.toReprR lhs.eval + Val.toReprR rhs.eval, rfl⟩

theorem eval_t {e : Expr T} : e.eval.val.toValType = T := by grind

def testExpr : Expr .I32 := .I32Add (.I32Lit 5) (.I32Add (.I32Lit 10) (.I32Lit 15))
def evalRes := testExpr.eval.val
#eval evalRes

def Expr.compile (e : Expr T) : Prog inp (T::inp) := match e with
| .I32Lit n => Prog.cons (.I32Const n) (Prog.nil)
| .F32Lit n => Prog.cons (.F32Const n) (Prog.nil)
| .I32Add lhs rhs => (Prog.concat lhs.compile rhs.compile).append (.I32Add)
| .I32Sub lhs rhs => (Prog.concat lhs.compile rhs.compile).append (.I32Sub)
| .F32Add lhs rhs => (Prog.concat lhs.compile rhs.compile).append (.F32Add)

def compiledExpr (inp : StackTypes := []) : Prog inp (.I32::inp) := testExpr.compile
def compileRes := evalProg [] compiledExpr
#eval compileRes

@[simp]
theorem eval_nil {st : Stack} {h : st.types = inpTys} : (evalProg' (@Prog.nil inpTys) st h).val = st := by
  unfold evalProg'; rfl

@[simp]
theorem concat_nil_l {a b : StackTypes} {lhs : Prog a b} : Prog.concat lhs Prog.nil = lhs := by
  induction lhs with
  | nil => rfl
  | cons op rest ih => unfold Prog.concat; rw [ih];

@[simp]
theorem concat_nil_r {a b : StackTypes} {rhs : Prog a b} : Prog.concat Prog.nil rhs = rhs := rfl

theorem prog_eval_concat : evalProg' (Prog.concat l r) st h = evalProg' r (evalProg' l st h) h'
  := by
    induction l generalizing st with
    | nil => simp
    | cons op_l rest_l ihl =>
        conv => left; unfold Prog.concat evalProg'; simp;
        rw [ihl]; rfl;

theorem eval_prog_append : evalProg' (Prog.append l op) st h = evalOp' op (evalProg' l st h) h'
  := by
    induction l generalizing st with
    | nil => simp [evalProg']
    | cons l_op rest ih => simp [evalProg']; rw [ih];

theorem compile_eq_eval' {T : ValType} {stypes : StackTypes} {st : Stack} {h : st.types = stypes}
  : ∀ (e : Expr T), (evalProg' e.compile st h).val = e.eval.val :: st
  := by
      intro e;
      induction e generalizing st stypes with
      | I32Lit n => conv => left; simp [evalProg', Expr.compile, evalOp'];
                    conv => right; simp [Expr.eval, TVal.toVal];
      | F32Lit n => conv => left; simp [evalProg', Expr.compile, evalOp'];
                    conv => right; simp [Expr.eval, TVal.toVal];
      | I32Add lhs rhs ihl ihr =>
          conv => left; unfold Expr.compile; rw [prog_append_assoc];
          rw [prog_eval_concat];
          conv => left; arg 1; arg 2; rw [ihl];
          rw [eval_prog_append];
          rotate_left;
          · grind
          · grind
          · conv => left; arg 1; arg 2; rw [ihr];
            conv => right; unfold Expr.eval;
            rw [eval_add] <;> grind;
      | I32Sub lhs rhs ihl ihr =>
          conv => left; unfold Expr.compile; rw [prog_append_assoc];
          rw [prog_eval_concat];
          · conv => left; arg 1; arg 2; rw [ihl];
            rw [eval_prog_append];
            rotate_left;
            · grind
            · grind
            · conv => left; arg 1; arg 2; rw [ihr];
              conv => right; unfold Expr.eval;
              rw [eval_sub] <;> grind;
      | F32Add lhs rhs ihl ihr =>
          conv => left; unfold Expr.compile; rw [prog_append_assoc];
          rw [prog_eval_concat];
          · conv => left; arg 1; arg 2; rw [ihl];
            rw [eval_prog_append];
            rotate_left;
            · grind
            · grind
            · conv => left; arg 1; arg 2; rw [ihr];
              conv => right; unfold Expr.eval;
              rw [eval_add_f32] <;> grind;

theorem compile_eq_eval : ∀ (e : Expr T), (evalProg' e.compile [] h).val = [e.eval.val] := by simp [compile_eq_eval'];
