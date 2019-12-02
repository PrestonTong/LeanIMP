inductive aexp : Type
  | ANum (n : nat)
  | AId (x : string)    
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)

inductive sinstr : Type
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult

def total_map (A : Type) := string -> A
/--/
def t_empty {A : Type} (v : A) : total_map A :=
  (fun _ : v).

def partial_map (A : Type) := total_map (option A)

def update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

def empty_st := (_ !-> 0) -/

def st := total_map nat

def aeval : st -> aexp -> nat
  | st (aexp.ANum n) := n
  | st (aexp.AId x) := st x
  | st (aexp.APlus  a1 a2) := (aeval st a1) + (aeval st a2)
  | st (aexp.AMinus a1 a2) := (aeval st a1) - (aeval st a2)
  | st (aexp.AMult  a1 a2) := (aeval st a1) * (aeval st a2)


def s_execute : st -> (list nat) -> (list sinstr) -> (list nat)
| state stack list.nil := stack
| state stack ((sinstr.SPush n)::prog) := s_execute state (n::stack) prog
| state stack ((sinstr.SLoad x)::prog) := s_execute state ((state x)::stack) prog
| state stack (sinstr.SPlus::prog) := match stack with
                                      | (h1::h2::stack_tail) := s_execute state ((h2 + h1)::stack_tail) prog
                                      | _ := s_execute state stack prog
                                      end
| state stack (sinstr.SMinus::prog) := match stack with
                                      | (h1::h2::stack_tail) := s_execute state ((h2 - h1)::stack_tail) prog
                                      | _ := s_execute state stack prog
                                      end                                    
| state stack (sinstr.SMult::prog) := match stack with
                                      | (h1::h2::stack_tail) := s_execute state ((h2 * h1)::stack_tail) prog
                                      | _ := s_execute state stack prog
                                      end

/-
def s_execute : st -> (list nat) -> (list sinstr) -> (list nat)
  | state stack list.nil := stack
  | state stack (h::t) := match h with
                            | sinstr.SPush n := s_execute state (n::stack) t
                            | sinstr.SLoad x := s_execute state ((state x)::stack) t
                            | sinstr.SPlus := match stack with
                                              | h1::h2::stack_tail := s_execute state ((h2 + h1)::stack_tail) t 
                                              | _ := s_execute state stack t
                                              end
                            | sinstr.SMinus := match stack with
                                              | h1::h2::stack_tail := s_execute state ((h2 - h1)::stack_tail) t 
                                              | _ := s_execute state stack t
                                                end
                            | sinstr.SMult := match stack with
                                                | h1::h2::stack_tail := s_execute state ((h2 * h1)::stack_tail) t 
                                                | _ := s_execute state stack t
                                                end
                         end-/

/-
def s_execute : st -> (list nat) -> (list sinstr) -> (list nat)
| state stack list.nil := stack
| state stack ((sinstr.SPush n)::prog) := s_execute state (n::stack) prog
| state stack ((sinstr.SLoad x)::prog) := s_execute state ((state x)::stack) prog
| state (h1::h2::stack_tail) (sinstr.SPlus::prog) := s_execute state ((h2 + h1)::stack_tail) prog
| state (h1::h2::stack_tail) (sinstr.SMinus::prog) := s_execute state ((h2 - h1)::stack_tail) prog                                 
| state (h1::h2::stack_tail) (sinstr.SMult::prog) := s_execute state ((h2 * h1)::stack_tail) prog
| state stack (_::prog) := s_execute state stack prog
-/

/-
example (empty_st : st)  :  (s_execute empty_st [] [sinstr.SPush 5, sinstr.SPush 3, sinstr.SPush 1, sinstr.SMinus]) 
    = [2, 5] :=
-/

def s_compile : aexp -> (list sinstr)
  | (aexp.ANum n) := [sinstr.SPush n]
  | (aexp.AId x) := [sinstr.SLoad x]                         
  | (aexp.APlus a1 a2) := s_compile a1 ++ s_compile a2 ++ [sinstr.SPlus]
  | (aexp.AMinus a1 a2)  := s_compile a1 ++ s_compile a2 ++ [sinstr.SMinus]
  | (aexp.AMult a1 a2) := s_compile a1 ++ s_compile a2 ++ [sinstr.SMult]

lemma s_compile_correct_prog : forall (state : st) (prog1 : list sinstr) (prog2 : list sinstr) (stack : list nat),
    s_execute state stack (prog1 ++ prog2) = s_execute state (s_execute state stack prog1) prog2 :=
begin
  intros state prog1 prog2,
  induction prog1,
  case list.nil { intro stack, simp, rw [s_execute] },
  case list.cons { intro stack, induction prog1_hd,
    case sinstr.SPush { simp, repeat { rw[s_execute] }, intros, destruct stack; rw prog1_ih; intros; refl},
    case sinstr.SLoad { simp, repeat { rw[s_execute] }, intros, destruct stack; rw prog1_ih; intros; refl},
    case sinstr.SPlus { simp, repeat { rw[s_execute] }, intros, cases stack, 
      case list.nil { rw prog1_ih, refl },
      case list.cons { cases stack_tl,
        case list.nil { rw prog1_ih, refl },
        case list.cons { repeat { rw[s_execute] }, rw prog1_ih }  
      }
    },
    case sinstr.SMinus { simp, repeat { rw[s_execute] }, intros, cases stack, 
      case list.nil { rw prog1_ih, refl },
      case list.cons { cases stack_tl,
        case list.nil { rw prog1_ih, refl },
        case list.cons { repeat { rw[s_execute] }, rw prog1_ih }  
      }
    },
    case sinstr.SMult { simp, repeat { rw[s_execute] }, intros, cases stack, 
      case list.nil { rw prog1_ih, refl },
      case list.cons { cases stack_tl,
        case list.nil { rw prog1_ih, refl },
        case list.cons { repeat { rw[s_execute] }, rw prog1_ih }  
      }
    }
  }
end

lemma s_compile_correct_prog' : forall (state : st) (prog1 : list sinstr) (prog2 : list sinstr) (stack : list nat),
    s_execute state stack (prog1 ++ prog2) = s_execute state (s_execute state stack prog1) prog2 :=
begin
  intros state prog1 prog2,
  induction prog1,
  case list.nil { intro stack, simp, rw [s_execute] },
  case list.cons { intro stack; induction prog1_hd;
    simp; repeat { rw[s_execute] }; intros;
    try { destruct stack; rw prog1_ih; intros; refl };
    try { cases stack, 
      case list.nil { rw prog1_ih, refl },
      case list.cons { cases stack_tl,
        case list.nil { rw prog1_ih, refl },
        case list.cons { repeat { rw[s_execute] }, rw prog1_ih }  
      } 
    }
  }
end


lemma s_compile_correct_general (state : st) (e : aexp) : forall (stack : list nat),
    s_execute state stack (s_compile e) = ((aeval state e) :: stack) :=
begin
  induction e;
  intro stack;
  try { refl }; intros; rw [aeval]; rw [s_compile];
  repeat { rw s_compile_correct_prog };
  rw [e_ih_a1];
  rw [e_ih_a2]; 
  repeat { rw [s_execute] };
  refl
end

theorem s_compile_correct (state : st) (e : aexp) :
  s_execute state [] (s_compile e) = [ aeval state e ] :=
begin
  intros,
  apply s_compile_correct_general
end