import Wasm

inductive CtlEntry
| Block
| Loop
deriving Repr

abbrev Ctls := List CtlEntry

structure WasmConf where
  types : StackTypes
  ctls : Ctls
deriving Repr

inductive Op' : WasmConf -> WasmConf -> Type where
  | Drop : Op' ⟨t :: ts, ctls⟩ ⟨ts, ctls⟩
  | I32Const (n : UInt32) : Op' ⟨ts, ctls⟩ ⟨.I32 :: ts, ctls⟩
  | F32Const (n : Float)  : Op' ⟨ts, ctls⟩ ⟨.F32 :: ts, ctls⟩
  | I32Add : Op' ⟨.I32 :: .I32 :: rest, ctls⟩ ⟨.I32 :: rest, ctls⟩
  | I32Sub : Op' ⟨.I32 :: .I32 :: rest, ctls⟩ ⟨.I32 :: rest, ctls⟩
  | F32Add : Op' ⟨.F32 :: .F32 :: rest, ctls⟩ ⟨.F32 :: rest, ctls⟩
  | Block : Op' ⟨ts, ctls⟩ ⟨ts, .Block :: ctls⟩
  | Loop : Op' ⟨ts, ctls⟩ ⟨ts, .Loop :: ctls⟩
  | End : Op' ⟨ts, ctl :: ctls⟩ ⟨ts,  ctls⟩
deriving Repr

inductive Prog' : WasmConf -> WasmConf -> Type where
  | nil : Prog' s s
  | cons {inp nxt out : WasmConf} (op : Op' inp nxt) (rest : Prog' nxt out) : Prog' inp out

infixr:50 " ;; " => Prog'.cons

def emptyConf : WasmConf := ⟨[], []⟩
def testProg' : Prog' emptyConf ⟨[.I32], []⟩ := 
  .I32Const 42 ;; 
  .I32Const 52 ;; 
  .I32Add ;;
  .Block;;
    .I32Const 42 ;; 
    .I32Const 52 ;; 
    .I32Add ;;
    .Drop ;;
  .End;;
  Prog'.nil
