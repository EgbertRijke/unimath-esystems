Require Export Foundations.hlevel2.hSet.

Definition ecarrier : UU :=
  total2 
    ( fun CFT : dirprod hSet (dirprod hSet hSet) => 
        dirprod 
          (pr1 (pr2 CFT) -> pr1 CFT)
          (pr2 (pr2 CFT) -> pr1 (pr2 CFT))
    ).

Definition eC (x : ecarrier) : hSet 
  := pr1 (pr1 x).

Definition eF (x : ecarrier) : hSet 
  := pr1 (pr2 (pr1 x)).

Definition eT (x : ecarrier) : hSet 
  := pr2 (pr2 (pr1 x)).

Definition eft (x : ecarrier) : eF x -> eC x 
  := pr1 (pr2 x). 

Definition ebd (x : ecarrier) : eT x -> eF x 
  := pr2 (pr2 x).

Definition ecarrierhom (x y : ecarrier) : UU 
  :=
  total2
    ( fun fCFT : dirprod (eC x -> eC y) (dirprod (eF x -> eF y) (eT x -> eT y))
      =>
        dirprod
          ( forall (A : eF x), (pr1 fCFT) (eft x A) = eft y ((pr1 (pr2 fCFT)) A))
          ( forall (t : eT x), (pr1 (pr2 fCFT)) (ebd x t) = ebd y ((pr2 (pr2 fCFT)) t))
    ).