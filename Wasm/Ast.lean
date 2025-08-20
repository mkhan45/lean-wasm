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

abbrev mapTypes : List Val -> List ValType := List.map Val.toValType

inductive Op : List ValType -> List ValType -> Type where
  | I32Const {rest : List ValType} (n : UInt32) : Op rest (ValType.I32 :: rest)
  | I32Add {rest : List ValType} : Op (ValType.I32 :: ValType.I32 :: rest) (ValType.I32 :: rest)

inductive Prog : List ValType -> List ValType -> Type where
  | nil : Prog s s
  | cons {inp nxt out : List ValType} (op : Op inp nxt) (rest : Prog nxt out) : Prog inp out

infixr:50 " ;; " => Prog.cons

def testProg : Prog [] [ValType.I32] := 
  Op.I32Const 42 ;; 
  Op.I32Const 52 ;; 
  Op.I32Add ;;
  Prog.nil

#check List.map_cons
def evalOp (inp : List Val) (op : Op (mapTypes inp) out) : {result : List Val // mapTypes result = out} := match inp, op with
| Val.I32 a :: Val.I32 b :: rest, Op.I32Add => 
  ⟨Val.I32 (a + b) :: rest, by unfold mapTypes; rw [List.map_cons, Val.toValType]⟩
| inp, Op.I32Const n => ⟨Val.I32 n :: inp, by unfold mapTypes; rw [List.map_cons, Val.toValType]⟩

def evalProg (inp : List Val) (prog : Prog (mapTypes inp) out) : {result : List Val // mapTypes result = out} := match prog with
| Prog.nil => ⟨inp, by rfl⟩
| Prog.cons op rest =>
    let ⟨step, h1⟩ := evalOp inp op
    evalProg step (h1 ▸ rest)

#eval (evalProg [] testProg).val
def evalOp' (op : Op inpTys outTys) (inp : List Val) (h : mapTypes inp = inpTys) 
  : {out : List Val // mapTypes out = outTys} := 
  match op with
  | Op.I32Const n => ⟨Val.I32 n :: inp, by unfold mapTypes at *; rw [List.map_cons, h, Val.toValType]⟩
  | Op.I32Add =>
      let (Val.I32 a) :: (Val.I32 b) :: xs := inp
      ⟨Val.I32 (a + b) :: xs, by simp at *; exact h⟩

def evalProg' (prog : Prog inpTys outTys) (inp : List Val) (h : mapTypes inp = inpTys) 
  : {out : List Val // mapTypes out = outTys} := match prog with
  | Prog.nil => ⟨inp, h⟩
  | Prog.cons op rest =>
    let ⟨step, h1⟩ := evalOp inp (h ▸ op)
    evalProg step (h1 ▸ rest)
