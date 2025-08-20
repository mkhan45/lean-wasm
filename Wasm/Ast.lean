import Aesop

inductive ValType : Type
  | I32
  deriving Repr

inductive Val : Type
  | I32 (n : UInt32)
  deriving Repr

def Val.toValType : Val -> ValType
  | I32 _ => ValType.I32

def mapTypes : List Val -> List ValType := List.map Val.toValType

theorem map_type_head : mapTypes (h :: xs) = h.toValType :: mapTypes xs := by rfl

def ValType.toType : ValType -> Type
| ValType.I32 => UInt32

inductive Op : List ValType -> List ValType -> Type where
  | I32Const {rest : List ValType} (n : UInt32) : Op rest (I32 :: rest)
  | I32Add {rest : List ValType} : Op (I32 :: I32 :: rest) (I32 :: rest)

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
  ⟨Val.I32 (a + b) :: rest, by rw [Val.toValType]; unfold mapTypes; rw [List.map_cons]⟩
| inp, Op.I32Const n => ⟨Val.I32 n :: inp, by unfold mapTypes; rw [List.map_cons]⟩

def evalProg (inp : List Val) (prog : Prog (mapTypes inp) out) : {result : List Val // mapTypes result = out} := match prog with
| Prog.nil => ⟨inp, by rfl⟩
| Prog.cons op rest =>
    let ⟨step, h1⟩ := evalOp inp op
    evalProg step (h1 ▸ rest)

#eval (evalProg [] testProg).val
