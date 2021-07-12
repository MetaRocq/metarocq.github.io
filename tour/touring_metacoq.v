(** * The MetaCoq Project
  MetaCoq is split into four components:
  - The "template" monad, dealing with reification of terms 
    and environments and monadic meta-programming of Coq.
  - The PCUIC development of the syntactic metatheory of Coq.
  - The SafeChecker package implementing reduction, conversion 
    and typechecking in a sound and complete way.
  - The Erasure package implementing verified extraction to 
    untyped lambda-calculus
*)

From Coq Require Import String List. (* .none *)
From MetaCoq.Template Require config utils All.
From MetaCoq.Template Require Import BasicAst TemplateMonad monad_utils.
Import MCMonadNotation. (* .none *)
Local Open Scope string_scope. (* .none *)
Import ListNotations. (* .none *)
Print Ast.term.
Print Ast.global_env.
Print Ast.global_decl.

(** ** The Template monad *)

(** *** Reification/Quoting *)
MetaCoq Quote Definition reifx := (fun x : nat => x).
Print reifx.

(** *** Reflection/Unquoting *)
MetaCoq Unquote Definition x := 
  (Ast.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Coq"], "nat") 0) 0 []).
Print x.

(** *** Monadic Meta-programs *)  
MetaCoq Run (tmBind (tmQuote (3 + 3)) tmPrint).

(** Support for interaction *)
MetaCoq Run (t <- tmLemma "foo44" nat ;;
             qt <- tmQuote t ;;
             t <- tmEval all t ;;
             tmPrint qt ;; tmPrint t).
Next Obligation.
  exact (3+2).
Defined.

(** ** PCUIC
  A specification of Coq's typing, reduction and conversion and its metatheory

  - Full algebraic universes supported everywhere
  - Universe polymorphism
  - Standard type theory with dependent products and let-ins
  - Inductive types and coinductive types
  - Constant and axiom declarations in a global environment *)

From MetaCoq.PCUIC Require Import PCUICAst PCUICReduction PCUICCumulativity PCUICPHOAS PCUICTyping PCUICSafeLemmata.

Print typing.

(** *** Metatheory *)
From MetaCoq.PCUIC Require PCUICConfluence PCUICSR PCUICPrincipality PCUICCanonicity.

Check PCUICSR.subject_reduction.
Check PCUICConfluence.red_confluence.
Check PCUICPrincipality.principal_type.
Print PCUICCanonicity.eval_ind_canonical.

(** ** Safe Checker *)
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICTypeChecker 
  PCUICSafeChecker Loader.

(** *** Verified conversion and type-checking *)
Check PCUICSafeConversion.isconv_term_sound.
Check PCUICSafeConversion.isconv_term_complete.
Check PCUICSafeChecker.infer_wf_env.

From MetaCoq.Examples Require Import metacoq_tour_prelude. (* .none *)

(** *** Type-checking Coq terms inside Coq

  We construct a proof of typing entirely within Coq, calling the typechecker to produce the derivation.
  The [check_inh] function takes a term and a type and verifies type-checking.
  The tactic [fill_inh] solves type inhabitance goals using [check_inh].
*)

Check check_inh.

(** We use a PHOAS input mode for reified terms (under [ [! _ ] ]), with a translation 
  to de Bruijn levels or indices for easier reading. *)  
Lemma identity_typing (u := Universe.make univ): 
  inh gctx_wf_env [] [! Π X @("X", Type u),'X → 'X].
Proof.
  (* We construct a term *)
  set (impl := [! λ s @ ("s", Type u), λ x @ ("x", 's), 'x]).
  (* Show that the empty context is well-formed  *)
  assert (wfΓ : ∥ wf_local gctx_wf_env [] ∥) by do 2 constructor.
 fill_inh impl.
Qed.
Print Assumptions identity_typing.

(** *** The extracted typechecker also runs in OCaml *)
MetaCoq SafeCheck (fun x : nat => x + 1).

(** ** Erasure *)
From MetaCoq.Erasure Require Import Erasure Loader.

(** *** Running erasure live in Coq *)

Definition erase {A} (term : A) : TemplateMonad unit := 
  p <- tmQuoteRecTransp term true ;;
  res <- tmEval lazy (A:=string) (erase_and_print_template_program p) ;;
  tmMsg res.

MetaCoq Run (erase (fun x : nat => (fun (A : Type) (a : A) => a) nat x + 1)).

(** *** Running the extracted erasure function in ML *)  
MetaCoq Erase
  ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).
