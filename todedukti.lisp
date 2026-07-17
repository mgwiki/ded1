					; usage:
					; megalodon .. -sexprinfo foo.mg > foo.sexpr
					; sbcl
					; (load "todedukti.lisp")
					; (mg-to-dedukti "foo.sexpr" "foo.dk")
					; or if you want a dk file without proofs:
					; (mg-to-dedukti "foo.sexpr" "foo.dk" nil)
(defun begin-poly-sec (g m)
  (case m
	(1 (format g "[a] "))
	(2 (format g "[a,b] "))
	(t nil)))

(defun end-poly-sec (g m) nil)

(defun tp-tpvar-plus (a)
  (case (car a)
        (AR (max (tp-tpvar-plus (cadr a)) (tp-tpvar-plus (caddr a))))
	(SET 0)
	(PROP 0)
	(TPVAR (1+ (cadr a)))
	(t (setq *badtp* a) (break))))

(defun tm-tpvar-plus (m)
  (case (car m)
        (TPAP (max (tm-tpvar-plus (cadr m)) (tp-tpvar-plus (caddr m))))
        (AP (max (tm-tpvar-plus (cadr m)) (tm-tpvar-plus (caddr m))))
        (IMP (max (tm-tpvar-plus (cadr m)) (tm-tpvar-plus (caddr m))))
	(ALL (max (tp-tpvar-plus (caddr m)) (tm-tpvar-plus (cadddr m))))
	(LAM (max (tp-tpvar-plus (caddr m)) (tm-tpvar-plus (cadddr m))))
	(t 0)))

(defun tp-str (a)
  (case (car a)
        (AR (format nil "(arr ~d ~d)" (tp-str (cadr a)) (tp-str (caddr a))))
	(SET "set")
	(PROP "prop")
	(TPVAR (nth (cadr a) '("a" "b")))
	(t (setq *badtp* a) (break))))

(defun tm-str (m)
  (case (car m)
        (TPAP (format nil "(~d ~d)" (tm-str (cadr m)) (tp-str (caddr m))))
					;        (AP (format nil "(ap _ _ ~d ~d)" (tm-str (cadr m)) (tm-str (caddr m))))
	(AP (format nil "(~d ~d)" (tm-str (cadr m)) (tm-str (caddr m))))
        (IMP (format nil "(Imp ~d ~d)" (tm-str (cadr m)) (tm-str (caddr m))))
;	(LAM (format nil "(lam ~d _ (~d => ~d))" (cadr m) (tp-str (caddr m)) (tm-str (cadddr m))))
;	(LAM (format nil "(~d => ~d)" (cadr m) (tm-str (cadddr m))))
	(LAM (format nil "(~d : Elem ~d => ~d)" (cadr m) (tp-str (caddr m)) (tm-str (cadddr m))))
	(ALL (format nil "(All ~d (~d => ~d))" (tp-str (caddr m)) (cadr m) (tm-str (cadddr m))))
	(DB (caddr m))
	(TMH (car (last m)))
	(t (setq *badtm* m) (break))))

(defun pf-str (d)
  (case (car d)
;        (TLAM (format nil "(~d => ~d)" (cadr d) ; (tp-str (caddr d))
;		      (pf-str (cadddr d))))
;        (PLAM (format nil "(~d => ~d)" (cadr d) ; (tm-str (caddr d))
;		      (pf-str (cadddr d))))
        (TLAM (format nil "(~d : Elem ~d => ~d)" (cadr d) (tp-str (caddr d)) (pf-str (cadddr d))))
        (PLAM (format nil "(~d : pf ~d => ~d)" (cadr d) (tm-str (caddr d)) (pf-str (cadddr d))))
	(PTPAP (format nil "(~d ~d)" (pf-str (cadr d)) (tp-str (caddr d))))
	(PTMAP (format nil "(~d ~d)" (pf-str (cadr d)) (tm-str (caddr d))))
	(PPFAP (format nil "(~d ~d)" (pf-str (cadr d)) (pf-str (caddr d))))
	(HYP (caddr d))
	(KNOWN (car (last d)))
	(t (setq *badpf* d) (break))))

(defun poly-prefix-all (m)
  (case m
	(1 "(a:type) -> ")
	(2 "(a:type) -> (b:type) -> ")
	(t "")))

(defun poly-prefix-lam (m)
  (case m
	(1 "(a => ")
	(2 "(a => (b => ")
	(t "")))

(defun poly-prefix-rparen (m)
  (case m
	(1 ")")
	(2 "))")
	(t "")))

(defun out-param (g nm h a)
  (let ((m (tp-tpvar-plus a)))
    (format g "~d : ~dElem ~d.~%" nm (poly-prefix-all m) (tp-str a))))

(defun out-prim (g nm a)
  (format g "~d : Elem ~d.~%" nm (tp-str a)))

(defun out-def (g nm a m)
  (let ((z (tp-tpvar-plus a)))
    (format g "def ~d : ~d Elem ~d~% := ~d~d~d.~%" nm (poly-prefix-all z) (tp-str a) (poly-prefix-lam z) (tm-str m) (poly-prefix-rparen z))))

(defun out-ax (g nm p)
  (let ((m (tm-tpvar-plus p)))
    (format g "~d : ~dpf ~d.~%" nm (poly-prefix-all m) (tm-str p))))

(defun out-thm (g nm p)
  (let ((m (tm-tpvar-plus p)))
    (when (> m 0) (error "dont do this please"))
    (format g "def ~d : pf ~d :=~%" nm (tm-str p))))

(defun out-qed (g d)
  (format g " ~d.~%" (pf-str d)))

(defun out-thm-no-pfs (g nm p)
  (let ((m (tm-tpvar-plus p)))
    (when (> m 0) (error "dont do this please"))
    (format g "~d : pf ~d.~%" nm (tm-str p))))

(defun mg-to-dedukti (mgsexpr dkout &optional (includepfs t))
  (let ((f (open mgsexpr :direction :input))
	(ll nil)
	(l nil))
    (loop while (setq l (read-line f nil nil)) do
	  (when (and (> (length l) 1) (eq (aref l 0) #\())
	    (push (read-from-string l) ll)))
    (close f)
    (setq ll (reverse ll))
    (let ((g (open dkout :direction :output :if-exists :supersede)))
      (format g "type : Type.~%arr : type -> type -> type.~%def Elem : type -> Type.~%[a,b] Elem (arr a b) --> Elem a -> Elem b.~%~%set : type.~%prop : type.~%def pf : Elem prop -> Type.~%~%def Ap : (a:type) -> (b:type) -> Elem (arr a b) -> Elem a -> Elem b.~%def Lam : (a:type) -> (b:type) -> (Elem a -> Elem b) -> Elem (arr a b).~%Imp : Elem prop -> Elem prop -> Elem prop.~%All : (a:type) -> (Elem a -> Elem prop) -> Elem prop.~%~%[a,b,m,n] Ap a b (Lam a b m n) --> m n. (; beta ;)~%[a,b,m,n] Lam a b (Ap a b m) --> m. (; eta ;)~%~%[p,q] pf (Imp p q) --> pf p -> pf q.~%[a,p] pf (All a p) --> (x:Elem a) -> pf (p x).~%")
      (dolist (x ll)
	(case (car x)
	      (PARAM (out-param g (cadr x) (caddr x) (nth 4 x)))
	      (PRIM (out-prim g (caddr x) (nth 4 x)))
	      (DEF (out-def g (cadr x) (nth 4 x) (nth 5 x)))
	      (AXIOM (out-ax g (cadr x) (nth 4 x)))
	      (THM
	       (if includepfs
		   (out-thm g (cadr x) (nth 5 x))
		 (out-thm-no-pfs g (cadr x) (nth 5 x))))
	      (QED (when includepfs (out-qed g (cadr x))))
	      (t nil)))
      (close g))))
