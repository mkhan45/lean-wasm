import Aesop

inductive ValType : Type
  | I32
  | F32
  deriving Repr

abbrev ValType.repr : ValType -> Type
| .I32 => UInt32
| .F32 => Float

inductive Val : Type
  | I32 (n : UInt32)
  | F32 (n : Float)
  deriving Repr

inductive TVal : ValType -> Type
| I32 (n : UInt32) : TVal .I32
| F32 (n : Float) : TVal .F32

@[simp]
abbrev Val.toValType (v: Val) : ValType := match v with
  | I32 _ => .I32
  | F32 _ => .F32

abbrev Val.toRepr (v : Val) : v.toValType.repr := match v with
| I32 n => n
| F32 n => n

abbrev TVal.toRepr (v : TVal T) : T.repr := match v with
| I32 n => n
| F32 n => n

abbrev TVal.toValR (tv : TVal T) : { v : Val // v.toValType = T } := match tv with
| I32 n => ⟨.I32 n, rfl⟩
| F32 n => ⟨.F32 n, rfl⟩

abbrev TVal.toVal (tv : TVal T) : Val := tv.toValR.val

abbrev TVal.ofVal (v : Val) : TVal v.toValType := match v with
| .I32 n => .I32 n
| .F32 n => .F32 n

abbrev Stack := List Val
abbrev StackTypes := List ValType

@[simp]
abbrev Stack.types (s : Stack) : StackTypes := List.map Val.toValType s

inductive Op : StackTypes -> StackTypes -> Type where
  | I32Const (n : UInt32) : Op inpTys (.I32 :: inpTys)
  | F32Const (n : Float) : Op inpTys (.F32 :: inpTys)
  | I32Add : Op (.I32 :: .I32 :: rest) (.I32 :: rest)
  | I32Sub : Op (.I32 :: .I32 :: rest) (.I32 :: rest)
  | F32Add : Op (.F32 :: .F32 :: rest) (.F32 :: rest)
  deriving Repr

inductive Prog : StackTypes -> StackTypes -> Type where
  | nil : Prog s s
  | cons {inp nxt out : StackTypes} (op : Op inp nxt) (rest : Prog nxt out) : Prog inp out
  /- deriving Repr -/

instance {inp out : StackTypes} : Repr (Prog inp out) where
  reprPrec prog _prec :=
    let rec toList {inp out : StackTypes} : (Prog inp out) -> List (Σ inp nxt : StackTypes, Op inp nxt)
      | .nil => []
      | .cons op rest => ⟨_, _, op⟩ :: toList rest
    
    let ops := toList prog
    match ops with
    | [] => "EmptyProg"
    | _ => 
      let opReprs := ops.map fun ⟨_, _, op⟩ => toString (repr op)
      String.intercalate ",\n" opReprs

def Prog.concat (fst : Prog a b) (snd : Prog b c) : Prog a c := match fst with
| .nil => snd
| .cons op rest => .cons op (rest.concat snd)

@[simp]
def Prog.append (prog : Prog a b) (op : Op b c) : Prog a c := match prog with
| .nil => Prog.cons op (Prog.nil)
| .cons op' rest => Prog.cons op' (rest.append op)

theorem prog_append_is_concat : Prog.append a op = Prog.concat a (Prog.cons op Prog.nil)
  := by
    induction a with
    | nil => rfl
    | cons a_op rest ih => unfold Prog.append Prog.concat; rw [ih];

theorem prog_concat_assoc : Prog.concat (Prog.concat a b) c = Prog.concat a (Prog.concat b c)
  := by
      induction a with
      | nil => simp [Prog.concat];
      | cons a_op rest iha => unfold Prog.concat; rw [<- iha]; rfl;

theorem prog_append_assoc : (Prog.concat a b).append op = Prog.concat a (b.append op)
  := by simp [prog_append_is_concat, prog_concat_assoc];

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
-- evalOp' is fundamentally different, since currying it with an op would produce
-- all of evalOp and also some useless functions which accept the wrong stack
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
    let ⟨step, h1⟩ := evalOp' op inp h
    evalProg' rest step h1
    /- evalProg step (h1 ▸ rest) -/

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
| I32 (v : UInt32) : TypedVal .I32
| F32 (v : Float) : TypedVal .F32

-- fundamentally different from just a stack,
-- which could only contain one variant of TypedVal
inductive TypedStack : StackTypes -> Type
  | nil : TypedStack []
  | cons (t : TypedVal t') (ts : TypedStack ts') : TypedStack (t' :: ts')

-- kind of better? makes a lot of the proof stuff implicit in the computation but
-- would be clunky
def evalOp'' (op : Op inpTys outTys) (inp : TypedStack inpTys) : TypedStack outTys := match op, inp with
| Op.I32Const n, inp =>
    TypedStack.cons (TypedVal.I32 n) inp
| Op.I32Add, TypedStack.cons (TypedVal.I32 a) (TypedStack.cons (TypedVal.I32 b) xs) => 
    TypedStack.cons (TypedVal.I32 (a + b)) xs
| Op.I32Sub, TypedStack.cons (TypedVal.I32 a) (TypedStack.cons (TypedVal.I32 b) xs) => 
    TypedStack.cons (TypedVal.I32 (a - b)) xs
| Op.F32Const n, inp =>
    TypedStack.cons (TypedVal.F32 n) inp
| Op.F32Add, TypedStack.cons (TypedVal.F32 a) (TypedStack.cons (TypedVal.F32 b) xs) => 
    TypedStack.cons (TypedVal.F32 (a + b)) xs

-- idk what this is good for
inductive WasmProg : Stack -> Type
| nil : WasmProg []
| cons (prev : WasmProg init) (op : Op init.types outTys) : WasmProg (evalOp init op)

def someProg :=
  WasmProg.cons (WasmProg.cons WasmProg.nil (.I32Const 5)) (.I32Const 10)

#check someProg
