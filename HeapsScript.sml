open HolKernel Parse boolLib bossLib;
open PrelimsTheory;
open ClosuresTheory;
open CodesTheory;

val _ = new_theory "Heaps";

(* ---------------------
           Heaps
   --------------------- *)

Type Heap = ``:(('a # num) # num) list``;
Type HA = ``:num``;
Type HC = ``:'a # HA``;
Type HE = ``:(('a HC) # HA) option``;

Datatype:
  heap =
    <|
      get : 'a Heap -> HA -> ('a HE) option;
      put : 'a Heap -> 'a HC -> HA -> ('a Heap) # HA;
    |>
End

Definition extended:
  extended H H' hImpl =
    ∀a. hImpl.get H a ≠ NONE ⇒ hImpl.get H a = hImpl.get H' a
End

Definition HR1:
  HR1 hImpl =
    ∀H g a H' b.
      hImpl.put H g a = (H', b) ⇒ hImpl.get H' b = SOME (SOME (g,a))
End

Definition HR2:
  HR2 hImpl =
    ∀H g a H' b.
      hImpl.put H g a = (H', b) ⇒ extended H H' hImpl
End

Definition HR:
  HR hImpl = (HR1 hImpl ∧ HR2 hImpl)
End

(*
Class heap PA :=
  {
    Heap : Type;
    HA : Set;
    HC := (PA * HA) % type;
    HE := option (HC * HA);
    get : Heap -> HA -> option HE;
    put : Heap -> HC -> HA -> Heap*HA;
    extended H H' := forall a, get H a <> None -> get H a = get H' a;
    HR1: forall H g a H' b, put H g a = (H', b) -> get H' b = Some (Some (g,a));
    HR2: forall H g a H' b, put H g a = (H', b) -> extended H H';
  }.

Coercion get : Heap >-> Funclass.
*)

(*
Section heap.
  Variable codeImpl : code.
  Variable C : Code.
  Variable heapImpl : heap PA.
  Implicit Type H : Heap.
*)

(* Reserved Notation "a ≫E_ H E" (at level 70, H at level 0, format "a '≫E_' H E"). *)
(* "a ≫E_ H E" := (representsEnv H a E). *)
(* HA -> list Clo -> Prop *)
Inductive representsEnv:
[~Nil:]
  (∀cImpl hImpl C H a. hImpl.get H a = SOME NONE ⇒ representsEnv cImpl hImpl C H a []) ∧
[~Cons:]
  (∀cImpl hImpl C H a b c p P F E.
         hImpl.get H a = SOME (SOME ((p, b), c)) ∧
         representsPro cImpl C p P ∧
         representsEnv cImpl hImpl C H b F ∧
         representsEnv cImpl hImpl C H c E ⇒
         representsEnv cImpl hImpl C H a ((closC P F)::E)
  )
End

Theorem representsEnv_functional:
  ∀cImpl hImpl C H. functional (representsEnv cImpl hImpl C H)
Proof
  simp[functional] >>
  Induct_on `representsEnv` >> rw[] (* 2 *)
  >- (fs[Once representsEnv_cases] >> fs[])
  >> pop_assum mp_tac >> rw[Once representsEnv_cases] >>
  metis_tac[representsPro_functional, functional]
QED

Theorem representsEnv_extend:
  ∀C cImpl hImpl H H' a E.
    extended H H' hImpl ⇒
    representsEnv cImpl hImpl C H a E ⇒
    representsEnv cImpl hImpl C H' a E
Proof
  Induct_on `representsEnv` >> rw[]
  >- (fs[extended] >>
      `hImpl.get H a ≠ NONE` by fs[] >>
      first_x_assum drule >> rw[] >>
      rw[Once representsEnv_cases])
  >> rw[Once representsEnv_cases] >>
  qexistsl_tac [`a'`, `a''`, `p`] >> rw[] >>
  fs[extended] >>
  `hImpl.get H a ≠ NONE` by fs[] >>
  first_x_assum drule >> rw[]
QED

(*  Reserved Notation "g ≫C_ H e" (at level 70,H at level 0, format "g '≫C_' H e"). *)
Inductive representsClos:
[~C:]
  (∀cImpl hImpl p a P E.
    representsPro cImpl C p P ∧
    representsEnv cImpl hImpl C H a E ⇒
    representsClos cImpl hImpl C H (p,a) (closC P E))
End

(*
  Inductive representsClos H : HC -> Clo -> Prop :=
    representsClos_C p a P E : p ≫p_C P -> a ≫E_H E -> (p,a) ≫C_H P/E
  where "g ≫C_ H e" := (representsClos H g e).
  Hint Constructors representsClos.

  Notation "(≫C( H ) )" := (representsClos H) (at level 0, format "'(≫C(' H ')' ')'").
  Notation "g ≫C_ H e" := 0.
  Notation "g ≫C_ H e" := (representsClos H g e).
*)

Theorem representsClos_extend:
  ∀cImpl H H' g e hImpl C.
    extended H H' hImpl ⇒
    representsClos cImpl hImpl C H g e ⇒
    representsClos cImpl hImpl C H' g e
Proof
  rw[] >> fs[Once representsClos_cases] >>
  metis_tac[representsEnv_extend]
QED

(* Notation "H .[ a , n ]" := (lookup H a n) (at level 1, format "H '.[' a ',' n ]"). *)
Definition lookup:
  lookup hImpl H a n =
    case (hImpl.get H a) of
      SOME (SOME (g, a')) =>
        (case n of
          0 => SOME g
        | SUC n => lookup hImpl H a' n)
      | _ => NONE
End

Theorem nth_error_unlinedEnv:
  ∀cImpl hImpl C H a E n e.
    representsEnv cImpl hImpl C H a E ⇒
    nth_error n E = SOME e ⇒
    ∃g. lookup hImpl H a n = SOME g ∧
        representsClos cImpl hImpl C H g e
Proof
  Induct_on `n` >> rw[] (* 2 *)
  >- (rw[Once lookup] >> fs[Once representsEnv_cases]
      >- (rw[] >> fs[Once nth_error])
      >> rw[] >> fs[Once nth_error] >> rw[] >>
      rw[Once representsClos_cases])
  >> qpat_x_assum `representsEnv _ _ _ _ _ _` mp_tac >>
  rw[Once representsEnv_cases, Once lookup]
  >- (rw[] >> fs[Once nth_error])
  >> rw[] >> fs[Once nth_error] >>
  metis_tac[]
QED

Theorem lookup_unlinedEnv:
  ∀cImpl hImpl C H a E n g.
    representsEnv cImpl hImpl C H a E ⇒
    lookup hImpl H a n = SOME g ⇒
    ∃e. nth_error n E = SOME e ∧
        representsClos cImpl hImpl C H g e
Proof
  Induct_on `n` >> rw[] (* 2 *)
  >- (rw[Once nth_error] >> fs[Once representsEnv_cases]
      >- (rw[] >> fs[Once lookup] >> gvs[])
      >> rw[] >> fs[Once lookup] >> rw[] >> gvs[] >>
      rw[Once nth_error, Once representsClos_cases])
  >> qpat_x_assum `representsEnv _ _ _ _ _ _` mp_tac >>
  rw[Once representsEnv_cases, Once nth_error]
  >- (rw[] >> fs[Once lookup])
  >> qpat_x_assum `lookup _ _ _ _ = _` mp_tac >>
  rw[Once lookup, Once nth_error] >>
  metis_tac[]
QED

Definition heapImpl:
  heapImpl =
    <|
      put := (λH g a. (H++[(g,a)], SUC (LENGTH H)));
      get := (λH a. case a of
                     | 0 => SOME NONE
                     | SUC a =>
                       (case nth_error a H of
                        | SOME (g,b) => SOME (SOME (g,b))
                        | NONE => NONE)
             )
    |>
End

val _ = export_theory ()