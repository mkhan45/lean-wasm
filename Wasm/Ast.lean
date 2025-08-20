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
  | I32Const {rest : StackTypes} (n : UInt32) : Op rest (ValType.I32 :: rest)
  | I32Add {rest : StackTypes} : Op (ValType.I32 :: ValType.I32 :: rest) (ValType.I32 :: rest)
  | F32Const {rest : StackTypes} (n : Float) : Op rest (ValType.F32 :: rest)
  | F32Add {rest : StackTypes} : Op (ValType.F32 :: ValType.F32 :: rest) (ValType.F32 :: rest)

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
macro "stack_op" : tactic => `(tactic| unfold Stack.types <;> rw [List.map_cons, Val.toValType])

def evalOp (inp : Stack) (op : Op inp.types out) : {result : Stack // result.types = out} := match inp, op with
| Val.I32 a :: Val.I32 b :: rest, Op.I32Add => 
    ⟨Val.I32 (a + b) :: rest, by stack_op⟩
| inp, Op.I32Const n => ⟨Val.I32 n :: inp, by stack_op⟩
| Val.F32 a :: Val.F32 b :: rest, Op.F32Add => 
    ⟨Val.F32 (a + b) :: rest, by stack_op⟩
| inp, Op.F32Const n => ⟨Val.F32 n :: inp, by stack_op⟩

def evalProg (inp : Stack) (prog : Prog (Stack.types inp) out) : {result : Stack // Stack.types result = out} := match prog with
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

def evalOp' (op : Op inpTys outTys) (inp : Stack) (h : Stack.types inp = inpTys) 
  : {out : Stack // Stack.types out = outTys} := 
  match op with
  | Op.I32Const n => ⟨Val.I32 n :: inp, by stack_op' h⟩
  | Op.I32Add =>
      let (Val.I32 a) :: (Val.I32 b) :: xs := inp
      ⟨Val.I32 (a + b) :: xs, by stack_op' h⟩
  | Op.F32Const n => ⟨Val.F32 n :: inp, by stack_op' h⟩
  | Op.F32Add =>
      let (Val.F32 a) :: (Val.F32 b) :: xs := inp
      ⟨Val.F32 (a + b) :: xs, by stack_op' h⟩

def evalProg' (prog : Prog inpTys outTys) (inp : Stack) (h : Stack.types inp = inpTys) 
  : {out : Stack // Stack.types out = outTys} := match prog with
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
