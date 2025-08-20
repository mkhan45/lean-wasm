import Aesop

inductive ValType : Type
  | I32
  | F32
  deriving Repr

inductive Val : Type
  | I32 (n : UInt32)
  | F32 (n : Float)
  deriving Repr

@[simp]
def Val.toValType : Val -> ValType
  | I32 _ => ValType.I32
  | F32 _ => ValType.F32

abbrev Stack := List Val
abbrev StackTypes := List ValType

@[simp]
abbrev Stack.types (s : Stack) : StackTypes := List.map Val.toValType s

inductive Op : StackTypes -> StackTypes -> Type where
  | I32Const (n : UInt32) : Op inpTys (ValType.I32 :: inpTys)
  | I32Add : Op (ValType.I32 :: ValType.I32 :: rest) (ValType.I32 :: rest)
  | I32Sub : Op (ValType.I32 :: ValType.I32 :: rest) (ValType.I32 :: rest)
  | F32Const (n : Float) : Op inpTys (ValType.F32 :: inpTys)
  | F32Add : Op (ValType.F32 :: ValType.F32 :: rest) (ValType.F32 :: rest)

inductive Prog : StackTypes -> StackTypes -> Type where
  | nil : Prog s s
  | cons {inp nxt out : StackTypes} (op : Op inp nxt) (rest : Prog nxt out) : Prog inp out

infixr:50 " ;; " => Prog.cons

def testProg : Prog [] [ValType.I32] := 
  Op.I32Const 42 ;; 
  Op.I32Const 52 ;; 
  Op.I32Add ;;
  Prog.nil

#check List.map_cons
macro "stack_op" : tactic => `(tactic| { unfold Stack.types; rw [List.map_cons, Val.toValType] })

def evalOp (inp : Stack) (op : Op inp.types outTys) : {out : Stack // out.types = outTys} := 
match inp, op with
| Val.I32 a :: Val.I32 b :: xs, Op.I32Add => ⟨Val.I32 (a + b) :: xs, by stack_op⟩
| Val.I32 a :: Val.I32 b :: xs, Op.I32Sub => ⟨Val.I32 (a - b) :: xs, by stack_op⟩
| inp, Op.I32Const n => ⟨Val.I32 n :: inp, by stack_op⟩
| Val.F32 a :: Val.F32 b :: xs, Op.F32Add => ⟨Val.F32 (a + b) :: xs, by stack_op⟩
| inp, Op.F32Const n => ⟨Val.F32 n :: inp, by stack_op⟩

def evalProg (inp : Stack) (prog : Prog inp.types out) : {result : Stack // result.types = out} := match prog with
| Prog.nil => ⟨inp, rfl⟩
| Prog.cons op rest =>
    let ⟨step, h1⟩ := evalOp inp op
    evalProg step (h1 ▸ rest)

macro "stack_op'" h:ident : tactic => `(tactic| {
  unfold Stack.types at *;
  repeat (rw [List.map_cons, Val.toValType] at *)
  repeat (rw [List.cons_inj_right]);
  repeat (rw [List.cons_inj_right] at $h:ident);
  exact $h
})

-- this is much more of a pain because op's inpTys are instantiated before we have inp,
-- so we need the extra h. Additionally, in the previous evalOp, somehow Lean figures
-- xs = inpTy automatically because it specializes more into the definition of Op?
-- something to do w/ definitional vs propositional equality? or more quantification order?
def evalOp' (op : Op inpTys outTys) (inp : Stack) (h : inp.types = inpTys) : {out : Stack // out.types = outTys} :=
  match h1 : op, h2 : inp with
  | Op.I32Const n, inp => ⟨Val.I32 n :: inp, by stack_op' h⟩
  | Op.I32Add, (Val.I32 a :: Val.I32 b :: xs) => ⟨Val.I32 (a + b) :: xs, by stack_op' h⟩
  | Op.I32Sub, Val.I32 a :: Val.I32 b :: xs => ⟨Val.I32 (a - b) :: xs, by stack_op' h⟩
  | Op.F32Const n, inp => ⟨Val.F32 n :: inp, by stack_op' h⟩
  | Op.F32Add, Val.F32 a :: Val.F32 b :: xs => ⟨Val.F32 (a + b) :: xs, by stack_op' h⟩

def evalProg' (prog : Prog inpTys outTys) (inp : Stack) (h : inp.types = inpTys) 
  : {out : Stack // out.types = outTys} := match prog with
  | Prog.nil => ⟨inp, h⟩
  | Prog.cons op rest =>
    let ⟨step, h1⟩ := evalOp inp (h ▸ op)
    evalProg step (h1 ▸ rest)

#eval (evalProg [] testProg).val
#eval (evalProg' testProg [] rfl).val

def testProgF : Prog [] [ValType.F32] := 
  Op.F32Const 42.5 ;; 
  Op.F32Const 52.9 ;; 
  Op.F32Add ;;
  Prog.nil
#eval (evalProg [] testProgF).val
#eval (evalProg' testProgF [] rfl).val

inductive TypedVal : ValType -> Type
  | I32 (n : UInt32) : TypedVal ValType.I32
  | F32 (n : Float) : TypedVal ValType.F32
  deriving Repr

inductive TypedStack : StackTypes -> Type
  | nil : TypedStack []
  | cons (t : TypedVal t') (ts : TypedStack ts') : TypedStack (t' :: ts')

-- i dont really understand why this is different that evalOp', but it works better
def evalOp'' (op : Op inpTys outTys) (inp : TypedStack inpTys) : TypedStack outTys := match op with
| Op.I32Const n => TypedStack.cons (TypedVal.I32 n) inp
| Op.I32Add =>
    let TypedStack.cons (TypedVal.I32 a) (TypedStack.cons (TypedVal.I32 b) xs) := inp
    TypedStack.cons (TypedVal.I32 (a + b)) xs
