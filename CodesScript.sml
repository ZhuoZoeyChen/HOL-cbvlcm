open HolKernel Parse boolLib bossLib;
open arithmeticTheory;
open listTheory;
open PrelimsTheory;
open ProgramsTheory;

val _ = new_theory "Codes";

(* ---------------------
    	   Codes
   --------------------- *)

Datatype:
  Com = retC | varC num | appC | lamC 'a
End

Type Code = ``:('a Com) list``;

Type PA = ``:num``;

Datatype:
	code =
		<|
    	   phi  : 'b -> 'a -> ('a Com) option;
    	   inc  : 'a -> 'a
    	|>
End

(* Reserved Notation "p ≫p_ C P" (at level 70,C at level 0, format "p '≫p_' C P"). *)
(* Code -> PA -> Pro -> Prop *)
(* Code -> num -> Pro -> Prop *)
Inductive representsPro:
[~Ret:]
	(∀cImpl p.
		cImpl.phi C p = SOME retC ⇒
		representsPro cImpl C p retT) ∧
[~Var:]
	(∀cImpl p P x.
		cImpl.phi C p = SOME (varC x) ∧ representsPro cImpl C (cImpl.inc p) P ⇒
		representsPro cImpl C p (varT x P)) ∧
[~Lam:]
	(∀cImpl p q P Q.
		cImpl.phi C p = SOME (lamC q) ∧ representsPro cImpl C (cImpl.inc p) P ∧
		representsPro cImpl C q Q ⇒
		representsPro cImpl C p (lamT Q P)) ∧
[~App:]
	(∀cImpl p P.
		cImpl.phi C p = SOME appC ∧ representsPro cImpl C (cImpl.inc p) P ⇒
		representsPro cImpl C p (appT P))
End

Theorem representsPro_functional:
	∀cImpl C. functional (representsPro cImpl C)
Proof
	rw[] >> simp[functional] >> Induct_on `representsPro` >> rw[] (* 4 *)
	>- (fs[Once representsPro_cases] >> fs[])
    >> pop_assum mp_tac >> rw[Once representsPro_cases]
QED

Definition codeImpl:
	codeImpl =
		<|	phi := (λC p.
		      case (nth_error p C) of
		      | SOME (lamC k) => SOME (lamC (p+k))
		      | SOME c => SOME c
		      | NONE => NONE);
		    inc := (λp. p+1)
		|>
End

(* (P:Pro) : list (Com nat) :=*)
Definition psi:
	psi P =
	    case P of
	    | retT => [retC]
	    | appT P => appC::psi P
	    | varT x P => varC x::psi P
	    | lamT Q P =>
		      let cP = psi P in
		      lamC (1 + LENGTH cP)::cP++psi Q
End

Theorem fetch_correct':
	∀C1 C2 P. representsPro codeImpl (C1++(psi P)++C2) (LENGTH C1) P
Proof
	Induct_on `P`
	>- (rw[Once representsPro_cases, codeImpl, AllCaseEqs()] >>
		`LENGTH C1 ≤ LENGTH C1` by rw[LESS_EQ_REFL] >>
		drule nth_error_app2 >> rw[] >>
		`nth_error (LENGTH C1) (C1 ⧺ (psi retT ⧺ C2)) = nth_error 0 (psi retT ⧺ C2)`
			by fs[] >> fs[APPEND_ASSOC] >> rw[nth_error, psi])
	>- (rw[Once representsPro_cases, AllCaseEqs()]
		>- (rw[codeImpl] >>
			`LENGTH C1 ≤ LENGTH C1` by rw[LESS_EQ_REFL] >>
			drule nth_error_app2 >> rw[] >>
			`nth_error (LENGTH C1) (C1 ⧺ (psi (varT n P) ⧺ C2)) =
			 nth_error 0 (psi (varT n P) ⧺ C2)` by fs[] >>
			fs[APPEND_ASSOC] >> rw[nth_error, Once psi])
		>> `representsPro codeImpl (C1 ⧺ psi (varT n P) ⧺ C2)
          	(LENGTH C1 + 1) P` suffices_by rw[codeImpl] >>
        rw[Once psi] >>
		`representsPro codeImpl ((C1 ++ [varC n]) ⧺ psi P ⧺ C2) (LENGTH (C1 ++ [varC n])) P`
			by fs[] >> fs[] >>
		`C1 ⧺ [varC n] ⧺ psi P ⧺ C2 = C1 ⧺ varC n::psi P ⧺ C2`
			suffices_by metis_tac[] >> rw[])
	>- (rw[Once representsPro_cases, AllCaseEqs()]
		>- (rw[codeImpl] >>
			`LENGTH C1 ≤ LENGTH C1` by rw[LESS_EQ_REFL] >>
			drule nth_error_app2 >> rw[] >>
			`nth_error (LENGTH C1) (C1 ⧺ (psi (appT P) ⧺ C2)) =
			 nth_error 0 (psi (appT P) ⧺ C2)` by fs[] >>
			fs[APPEND_ASSOC] >> rw[nth_error, Once psi])
		>> `representsPro codeImpl (C1 ⧺ psi (appT P) ⧺ C2)
          	(LENGTH C1 + 1) P` suffices_by rw[codeImpl] >>
		rw[Once psi] >>
		`representsPro codeImpl ((C1 ++ [appC]) ⧺ psi P ⧺ C2) (LENGTH (C1 ++ [appC])) P`
			by fs[] >> fs[] >>
		`C1 ⧺ [appC] ⧺ psi P ⧺ C2 = C1 ⧺ appC::psi P ⧺ C2`
			suffices_by metis_tac[] >> rw[])
	>> rw[Once representsPro_cases] >>
	qexists_tac `LENGTH (psi P') + 1 + LENGTH C1` >> rw[] >> rw[Once psi]
	>- (rw[codeImpl, AllCaseEqs(), PULL_EXISTS] >>
		`LENGTH C1 ≤ LENGTH C1` by rw[LESS_EQ_REFL] >>
		drule nth_error_app2 >> rw[] >>
		`nth_error (LENGTH C1) (C1 ⧺ (lamC (LENGTH (psi P') + 1)::(psi P' ⧺ psi P) ⧺ C2)) =
		 nth_error 0 (lamC (LENGTH (psi P') + 1)::(psi P' ⧺ psi P) ⧺ C2)`
		 	by fs[] >> fs[APPEND_ASSOC] >>
		rw[nth_error])
	>- (`representsPro codeImpl (C1 ⧺ lamC (LENGTH (psi P') + 1)::(psi P' ⧺ psi P) ⧺ C2)
         (LENGTH C1 + 1) P'`
		 	suffices_by rw[codeImpl, AllCaseEqs(), PULL_EXISTS] >>
		`representsPro codeImpl ((C1 ⧺ [lamC (LENGTH (psi P') + 1)]) ⧺ psi P' ⧺ (psi P ⧺ C2))
					   (LENGTH (C1 ⧺ [lamC (LENGTH (psi P') + 1)]))
					   P'` by fs[] >> fs[] >>
		`C1 ⧺ [lamC (LENGTH (psi P') + 1)] ⧺ psi P' ⧺ psi P ⧺ C2 =
		 C1 ⧺ lamC (LENGTH (psi P') + 1)::(psi P' ⧺ psi P) ⧺ C2`
		 	suffices_by metis_tac[] >> rw[])
	>> `representsPro codeImpl (C1 ⧺ lamC (LENGTH (psi P') + 1)::(psi P' ⧺ psi P) ⧺ C2)
        (LENGTH C1 + (LENGTH (psi P') + 1)) P`
        	suffices_by rw[codeImpl, AllCaseEqs(), PULL_EXISTS] >>
	`representsPro codeImpl ((C1 ⧺ lamC (LENGTH (psi P') + 1) :: psi P') ⧺ psi P ⧺ C2)
					   (LENGTH (C1 ⧺ lamC (LENGTH (psi P') + 1) :: psi P'))
					   P` by fs[] >> fs[ADD1] >>
	`C1 ⧺ lamC (LENGTH (psi P') + 1)::psi P' ⧺ psi P ⧺ C2 =
	 C1 ⧺ lamC (LENGTH (psi P') + 1)::(psi P' ⧺ psi P) ⧺ C2`
	 	suffices_by metis_tac[] >> rw[]
QED

Theorem fetch_correct:
	∀P. representsPro codeImpl (psi P) 0 P
Proof
	rw[] >>
	`representsPro codeImpl ([]++(psi P)++[]) (LENGTH ([]: num Com list)) P`
		by metis_tac[fetch_correct'] >>
	fs[]
QED

val _ = export_theory ()