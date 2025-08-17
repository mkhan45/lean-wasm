inductive ValType : Type
  | I32

inductive Val where
  | I32 (n : UInt32)

def Val.toValType : Val -> ValType
  | I32 _ => ValType.I32

def mapTypes : List Val -> List ValType := List.map Val.toValType

def ValType.toType : ValType -> Type
| ValType.I32 => UInt32

inductive Op : List ValType -> List ValType -> Type where
  | I32Const {rest : List ValType} (n : UInt32) : Op rest (I32 :: rest)
  | I32Add {rest : List ValType} : Op (I32 :: I32 :: rest) (I32 :: rest)

inductive Prog : List ValType -> List ValType -> Type where
  | nil : Prog s s
  | cons {inp nxt out : List ValType} (op : Op inp nxt) (rest : Prog nxt out) : Prog inp out

infixr:50 " ;; " => Prog.cons

def testProg : Prog [] [I32] := 
  Op.I32Const 42 ;; 
  Op.I32Const 52 ;; 
  Op.I32Add ;;
  Prog.nil

def evalOp (op : Op inp out) (st : List Val) (h : mapTypes st = inp) : List Val := match (op, st) with
| (Op.I32Const n, _) => Val.I32 n :: st
| (Op.I32Add, Val.I32 a :: Val.I32 b :: xs) => Val.I32 (a + b) :: xs
| (Op.I32Add, s) => False.elim (by sorry)
