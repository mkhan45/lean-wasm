import Wasm

inductive CtlTy
| Block
| Loop
deriving Repr

inductive CtlEntry : CtlTy -> Type
| Block (pc : Nat) : CtlEntry .Block
| Loop (pc : Nat) : CtlEntry .Loop
deriving Repr

abbrev CtlTys := List CtlTy

inductive Ctls : CtlTys -> Type
| nil : Ctls []
| cons (ctl : CtlEntry t) (xs : Ctls ts) : Ctls (t :: ts)

infixr:50 " ;; " => Ctls.cons

structure WasmConf where
  types : StackTypes
  ctl_types : CtlTys
deriving Repr

inductive Op' : WasmConf -> WasmConf -> Type where
  | Nop : Op' c c
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

def Prog'.atPc (prog : Prog' ic oc) (pc : Nat) : Σ inp nxt, Op' inp nxt := match prog, pc with
| .cons op xs, .zero => ⟨_, _, op⟩
| .cons _ xs, .succ n => xs.atPc n
| .nil, _ => ⟨ic, ic, .Nop⟩

infixr:50 " ;; " => Prog'.cons

structure WasmState (conf : WasmConf) where
  stack : TStack conf.types
  ctls : Ctls conf.ctl_types
  pc : Nat
  code : Prog' start_conf end_conf

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

def Op'.eval (op : Op' in_conf out_conf) (in_state : WasmState in_conf) : WasmState out_conf :=
  let ⟨stack, ctls, pc, code⟩ := in_state
  match op, stack with
  | Nop, xs => ⟨xs, ctls, pc + 1, code⟩
  | Drop, _ :: xs => ⟨xs, ctls, pc + 1, code⟩
  | I32Const n, xs => ⟨.I32 n :: xs, ctls, pc + 1, code⟩
  | F32Const n, xs => ⟨.F32 n :: xs, ctls, pc + 1, code⟩
  | I32Add, .I32 a :: .I32 b :: xs => ⟨.I32 (b + a) :: xs, ctls, pc + 1, code⟩
  | I32Sub, .I32 a :: .I32 b :: xs => ⟨.I32 (b - a) :: xs, ctls, pc + 1, code⟩
  | F32Add, .F32 a :: .F32 b :: xs => ⟨.F32 (b + a) :: xs, ctls, pc + 1, code⟩
  | Block, st => ⟨st, .cons (.Block pc) ctls, pc + 1, code⟩
  | Loop, st => ⟨st, .cons (.Loop pc) ctls, pc + 1, code⟩
  | End, st => match ctls with | .cons _ cxs => ⟨st, cxs, pc + 1, code⟩

-- to do this cleanly, probably need to put the pc and code as part of WasmState somehow
def WasmState.step (st : WasmState conf) : WasmState conf' := sorry
