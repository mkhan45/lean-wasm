import Wasm

inductive Expr : ValType -> Type
| I32Lit (n : UInt32) : Expr .I32
| F32Lit (n : Float) : Expr .F32
| I32Add (lhs : Expr .I32) (rhs : Expr .I32) : Expr .I32
| I32Sub (lhs : Expr .I32) (rhs : Expr .I32) : Expr .I32
| F32Add (lhs : Expr .F32) (rhs : Expr .F32) : Expr .F32

def Expr.eval' (e : Expr T) : TVal T := match e with
| .I32Lit n => .I32 n
| .F32Lit n => .F32 n
| .I32Add lhs rhs => .I32 $ lhs.eval'.toRepr + rhs.eval'.toRepr
| .I32Sub lhs rhs => .I32 $ lhs.eval'.toRepr - rhs.eval'.toRepr
| .F32Add lhs rhs => .F32 $ lhs.eval'.toRepr + rhs.eval'.toRepr

theorem val_repr (v : { v : Val // v.toValType = T}) : v.val.toValType.repr = T.repr := by rw [v.property];

def Expr.eval'' (e : Expr T) : { v : Val // v.toValType = T } := match e with
| .I32Lit n => ⟨.I32 n, rfl⟩
| .F32Lit n => ⟨.F32 n, rfl⟩
| .I32Add lhs rhs => ⟨.I32 $ Val.toReprR lhs.eval'' + Val.toReprR rhs.eval'', rfl⟩
      /- let ⟨lhs_e, hl⟩ := lhs.eval'' -/
      /- let ⟨rhs_e, hr⟩ := rhs.eval'' -/
      /- let hlr : lhs_e.toValType.repr = UInt32 := by rw [hl]; -/
      /- let hrr : rhs_e.toValType.repr = UInt32 := by rw [hr]; -/
      /- ⟨.I32 $ (val_repr ▸ lhs_e.toRepr) + (hrr ▸ rhs_e.toRepr), rfl⟩ -/
| .I32Sub lhs rhs => ⟨.I32 $ Val.toReprR lhs.eval'' - Val.toReprR rhs.eval'', rfl⟩
| .F32Add lhs rhs => ⟨.F32 $ Val.toReprR lhs.eval'' + Val.toReprR rhs.eval'', rfl⟩

def Expr.eval (e : Expr T) : T.repr := 
  let tv := e.eval'
  let ⟨v, h⟩ := tv.toValR
  have h' : v.toValType.repr = T.repr := by rw [h];
  h ▸ v.toRepr

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
theorem concat_nil_l {a b : StackTypes} {lhs : Prog a b} : Prog.concat lhs Prog.nil = lhs := by
  induction lhs with
  | nil => rfl
  | cons op rest ih => unfold Prog.concat; rw [ih];

@[simp]
theorem concat_nil_r {a b : StackTypes} {rhs : Prog a b} : Prog.concat Prog.nil rhs = rhs := rfl

/- theorem concat_cons_eval {a b c: StackTypes} -/
/-   (left : Prog a b) (right : Prog b c) {op : Op b s} {rrest : Prog s c} -/
/-   (st : Stack) (h : st.types = a) -/
/-   : (right = Prog.cons op rrest) -> -/
/-       let ⟨lstack, lh⟩ := evalProg' left st h -/
/-       let ⟨step, sh⟩ := evalOp' op lstack lh -/
/-       let ⟨final, rh⟩ := evalProg' rrest step sh -/
/-       evalProg' (Prog.concat left right) st h = evalProg' rrest step sh -/
/- := by -/ 
/-   simp; intro right_def; -/
/-   induction left with -/
/-   | nil => unfold evalProg'; simp; cases right with -/
/-                                    | nil => contradiction; -/
/-                                    | cons op' rrest' => rw [right_def, ← evalProg'.eq_def]; -/
/-   | cons l_op lrest ih => unfold evalProg'; simp; cases right with -/
/-                                                   | nil => contradiction; -/
/-                                                   | cons op' rrest' => rw [right_def, <- evalProg'.eq_def]; sorry -/

theorem concat_cons_eval {a b c: StackTypes}
  (left : Prog a b) (op : Op b s) (rrest : Prog s c)
  (st : Stack) (h : st.types = a)
  :
      let ⟨lstack, lh⟩ := evalProg' left st h
      let ⟨step, sh⟩ := evalOp' op lstack lh
      let ⟨final, rh⟩ := evalProg' rrest step sh
      evalProg' (Prog.concat left (op ;; rrest)) st h = evalProg' rrest step sh
:= by
  simp; induction rrest with
  | nil => conv => right; unfold evalProg';
           conv => left; unfold evalProg' Prog.concat;
           sorry
  | cons op rest rest_ih => sorry

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
  | cons r_op rrest r_ih =>
      rw [Subtype.ext_iff];
      conv => right; unfold evalProg'; dsimp;
      let ⟨lstack, lh⟩ := evalProg' left astack ah
      let ⟨step, sh⟩ := evalOp' r_op lstack lh
      let ⟨final, rh⟩ := evalProg' rrest step sh;
      /- rw [concat_cons_eval]; -/

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

-- TODO: rewrite without progResHead, insteal have smth like (eval e) :: stack
/- theorem compile_head_eq_eval : ∀ (e : Expr T), eval_eq_compile e := by -/
/-   intro e; unfold eval_eq_compile; intro prog compile_res; simp; -/
/-   induction e with -/
/-   | I32Lit n => -/
/-       unfold progResHead; -/
/-       have hc : compile_res = ⟨[Val.I32 n], by simp⟩ := by -/
/-         (unfold compile_res; unfold prog Expr.compile evalProg evalOp evalProg; dsimp) -/
/-       rw [hc]; dsimp; rfl; -/
/-   | F32Lit n => -/
/-       unfold progResHead; -/
/-       have hc : compile_res = ⟨[Val.F32 n], by simp⟩ := by -/
/-         (unfold compile_res; unfold prog Expr.compile evalProg evalOp evalProg; dsimp) -/
/-       rw [hc]; dsimp; -/
/-       unfold Expr.eval; rfl; -/
/-   | I32Add lhs rhs lhs_ih rhs_ih => -/
/-       have hc : compile_res = sorry := by ( -/
/-         unfold compile_res prog Expr.compile; -/
/-         unfold progResHead at *; -/

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

theorem compile_eq_eval {T : ValType} {stypes : StackTypes} {st : Stack} {h : st.types = stypes}
  : ∀ (e : Expr T), (evalProg' e.compile st h).val = e.eval'.toVal :: st
  := by
      intro e;
      induction e generalizing st stypes with
      | I32Lit n => conv => left; simp [evalProg', Expr.compile, evalOp'];
                    conv => right; simp [Expr.eval', TVal.toVal];
      | F32Lit n => conv => left; simp [evalProg', Expr.compile, evalOp'];
                    conv => right; simp [Expr.eval', TVal.toVal];
      | I32Add lhs rhs ihl ihr =>
          conv => left; unfold Expr.compile; rw [prog_append_assoc];
          rw [prog_eval_concat];
          · conv => left; arg 1; arg 2; rw [ihl];
            rw [eval_prog_append];
            rotate_left;
            -- proving type hypotheses
            · grind -- idk if this is a good use of grind
            · grind
            · conv => left; arg 1; arg 2; rw [ihr];
              simp [Expr.eval'];
              -- scuffed here bc of TVal/Val differences :/
              unfold evalOp'; simp;
              sorry

theorem compile_eq_eval' {T : ValType} {stypes : StackTypes} {st : Stack} {h : st.types = stypes}
  : ∀ (e : Expr T), (evalProg' e.compile st h).val = e.eval''.val :: st
  := by
      intro e;
      induction e generalizing st stypes with
      | I32Lit n => conv => left; simp [evalProg', Expr.compile, evalOp'];
                    conv => right; simp [Expr.eval', TVal.toVal];
                    rfl;
      | F32Lit n => conv => left; simp [evalProg', Expr.compile, evalOp'];
                    conv => right; simp [Expr.eval', TVal.toVal];
                    rfl;
      | I32Add lhs rhs ihl ihr =>
          conv => left; unfold Expr.compile; rw [prog_append_assoc];
          rw [prog_eval_concat];
          · conv => left; arg 1; arg 2; rw [ihl];
            rw [eval_prog_append];
            rotate_left;
            · grind
            · grind
            · conv => left; arg 1; arg 2; rw [ihr];
              conv => right; unfold Expr.eval'';
              rw [eval_add] <;> grind
      | I32Sub lhs rhs ihl ihr =>
          sorry
  /- have ⟨res, h⟩ := progResHead compile_res; -/
  /- have h' : T.repr = res.toValType.repr := by rw [h]; -/
  /- show (res.toRepr = h' ▸ e.eval); -/
  /- induction e with -/
