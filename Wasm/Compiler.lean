import Wasm

inductive Expr : ValType -> Type
| I32Lit (n : UInt32) : Expr .I32
| F32Lit (n : Float) : Expr .F32
| I32Add (lhs : Expr .I32) (rhs : Expr .I32) : Expr .I32
| I32Sub (lhs : Expr .I32) (rhs : Expr .I32) : Expr .I32
| F32Add (lhs : Expr .F32) (rhs : Expr .F32) : Expr .F32

def Expr.eval (e : Expr T) : T.repr := match e with
| .I32Lit n => n
| .F32Lit n => n
| .I32Add lhs rhs => lhs.eval + rhs.eval
| .I32Sub lhs rhs => lhs.eval - rhs.eval
| .F32Add lhs rhs => lhs.eval + rhs.eval

def testExpr : Expr .I32 := .I32Add (.I32Lit 5) (.I32Add (.I32Lit 10) (.I32Lit 15))
def evalRes := testExpr.eval
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

def progResHead (progRes : { result : Stack // result.types = (x::xs) }) : { val : Val // val.toValType = x } :=
  let ⟨st, h⟩ := progRes
  let hd::tl := st
  have h' : hd.toValType = x := by
    unfold Stack.types at h;
    rw [List.map_cons, List.cons_eq_cons] at h; apply h.left;
  ⟨hd, h'⟩

def eval_eq_compile (e : Expr T) : Prop :=
  let prog := @e.compile T []
  let compile_res := evalProg [] prog
  let ⟨res, h⟩ := progResHead compile_res
  let eval_res := e.eval
  have h' : T.repr = res.toValType.repr := by rw [h]
  res.toRepr = (h' ▸ eval_res)

def test_expr_eq : Bool :=
  let prog := testExpr.compile
  let compile_res := evalProg [] prog
  let ⟨res, h⟩ := progResHead compile_res
  have h' : UInt32 = res.toValType.repr := by rw [h]
  let res : UInt32 := (h' ▸ res.toRepr)
  let eval_res := testExpr.eval
  res == eval_res
#eval test_expr_eq

@[simp]
theorem eval_nil {st : Stack} {h : st.types = inpTys} : (evalProg' (@Prog.nil inpTys) st h).val = st := by
  unfold evalProg'; rfl

/- @[simp] -/
/- theorem prog_cast_nil {a b : StackTypes} (h : a = b) : (h ▸ (@Prog.nil a)) = (@Prog.nil b) := by -/
/-   subst h; rfl -/

@[simp]
theorem concat_nil {a b : StackTypes} {lhs : Prog a b} : Prog.concat lhs Prog.nil = lhs := by
  induction lhs with
  | nil => rfl
  | cons op rest ih => unfold Prog.concat; rw [ih];

theorem concat_eval {a b c : StackTypes} 
  (left : Prog a b) (right : Prog b c) 
  (astack : Stack) (ah : astack.types = a)
  :
    let ⟨bstack, bh⟩ := evalProg' left astack ah
    evalProg' (Prog.concat left right) astack ah = evalProg' right bstack bh
:= by
  dsimp;
  induction right with
  | nil => aesop
  | cons r_op rrest r_ih => sorry
  /- induction left with -/
  /- | @nil s => -/
  /-     conv => rhs; arg 2; rw [eval_nil]; -/
  /-     unfold Prog.concat; -/ 
  /-     rfl -/
  /- | cons l_op lrest l_ih => -/
  /-     have : -/ 
      /- induction right with -/
      /- | @nil s => rw [concat_nil]; rfl -/
      /- | cons r_op rrest r_ih => -/
      /-     conv => rhs; -/ 

          

        
  /- obtain ⟨bstack, bh⟩ := (evalProg astack (ah ▸ left)) -/
  /- show _ = _; -/
  /- induction h : left generalizing astack with -/
  /- | @nil s => -/ 

  /-     sorry -/

theorem compile_head_eq_eval : ∀ (e : Expr T), eval_eq_compile e := by
  intro e; unfold eval_eq_compile; intro prog compile_res; simp;
  induction e with
  | I32Lit n =>
      unfold progResHead;
      have hc : compile_res = ⟨[Val.I32 n], by simp⟩ := by
        (unfold compile_res; unfold prog Expr.compile evalProg evalOp evalProg; dsimp)
      rw [hc]; dsimp; rfl;
  | F32Lit n =>
      unfold progResHead;
      have hc : compile_res = ⟨[Val.F32 n], by simp⟩ := by
        (unfold compile_res; unfold prog Expr.compile evalProg evalOp evalProg; dsimp)
      rw [hc]; dsimp;
      unfold Expr.eval; rfl;
  | I32Add lhs rhs lhs_ih rhs_ih =>
      unfold progResHead compile_res;
      have hc : compile_res = sorry := by (
        unfold compile_res prog Expr.compile;
        have : evalProg [] (Prog.concat lhs.compile rhs.compile) = sorry := by (
          unfold Prog.concat; dsimp; sorry)
  /- have ⟨res, h⟩ := progResHead compile_res; -/
  /- have h' : T.repr = res.toValType.repr := by rw [h]; -/
  /- show (res.toRepr = h' ▸ e.eval); -/
  /- induction e with -/
