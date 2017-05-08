(declaim (optimize (speed 0) (debug 3)))

(in-package #:containers)

;;; ------------------ my exploration ------------------------------------------

;;; this classifier allows us to pass cons pairs as coordinates
(defun cons-classifier (x y)
  (cond ((and (< (car x) (car y))
              (>= (cdr x) (cdr y)))
         :TOP-LEFT)
        ((and (>= (car x) (car y))
              (>= (cdr x) (cdr y)))
         :TOP-RIGHT)
        ((and (>= (car x) (car y))
              (< (cdr x) (cdr y)))
         :BOTTOM-RIGHT)
        ((and (< (car x) (car y))
              (< (cdr x) (cdr y)))
         :BOTTOM-LEFT)
        (T (error "ran out of options"))))

;; This is example of running the following code
;; as we can see the children are added correctly
;; #<QUAD-TREE-NODE {1002108043}>
;; --------------------
;; Class: #<STANDARD-CLASS METABANG.CL-CONTAINERS::QUAD-TREE-NODE>
;; --------------------
;; Group slots by inheritance [ ]
;; Sort slots alphabetically  [X]
;;
;; All Slots:
;; [ ]  BOTTOM-LEFT-CHILD  = @2=#<QUAD-TREE-NODE (-1 . -1)>
;; [ ]  BOTTOM-RIGHT-CHILD = #<QUAD-TREE-NODE (1 . -1)>
;; [ ]  ELEMENT            = (0 . 0)
;; [ ]  PARENT             = NIL
;; [ ]  TOP-LEFT-CHILD     = #<QUAD-TREE-NODE (-1 . 1)>
;; [ ]  TOP-RIGHT-CHILD    = #<QUAD-TREE-NODE (1 . 1)>
;; [ ]  TREE               = @0=#<QUAD-TREE {1002040973}>



(defun test-exploration ()
  (let ((c (make-instance 'quad-tree :classifier 'cons-classifier )))
    (unless (eq (size c) 0)
      (cerror "wrong size ~a , but 0 expected" (size c)))
    (insert-item c (make-node-for-container c (cons 0 0)))
    (unless (= (size c) 1)
      (cerror "continue" "error: got ~a, expected 1" (size c)))
    (insert-item c (make-node-for-container c (cons -1 1)))
    (insert-item c (make-node-for-container c (cons 1 1)))
    (insert-item c (make-node-for-container c (cons 1 -1)))
    (insert-item c (make-node-for-container c (cons -1 -1)))
    (unless (= (size c) 5)
      (cerror "continue" "error: got ~a expected 5" (size c)))
    (cerror "hurray" "tree examiner ~a" c)
    (empty! c)
    (unless (eq (size c) 0)
      (cerror "continue" "wrong size ~a , but 0 expected" (size c)))
    ))


;;; ----------------------------------------------------------------------------

;;; quad-tree

(defclass* quad-tree (initial-contents-mixin
                        classified-container-mixin
                        findable-container-mixin
                        iteratable-container-mixin
                        container-uses-nodes-mixin
                        rooted-tree-container
                        concrete-container)
  ((size 0))
  :automatic-accessors
  :automatic-initargs
  (:default-initargs
    :key 'identity
    :test 'eq))

(defclass* four-child-node (parent-node-mixin)
  ((top-left-child :initform nil
                   :accessor top-left-child)
   (top-right-child :initform nil
                    :accessor top-right-child)
   (bottom-left-child :initform nil
                      :accessor bottom-left-child)
   (bottom-right-child :initform nil
                       :accessor bottom-right-child)))


(defclass* quad-tree-node (four-child-node)
  ((tree :initform nil
         :initarg :tree
         :accessor tree)))


(defmethod make-node-for-container ((tree quad-tree) (item t) &key)
  (if item
    (make-instance 'quad-tree-node
      :element item
      :tree tree)
    nil))


(defmethod node-empty-p ((node quad-tree-node))
  (null (element node)))


(defmethod print-object ((o quad-tree-node) stream)
  (print-unreadable-object (o stream :type t)
    (format stream "~A" (element o))))


(defgeneric notify-element-of-child-status (element status)
  (:documentation "This is called to allow the element to know its
status as a child. Useful for quad tree elements, where an element's position
relative to its parent could be relevant to the element. Status is one of:
:TOP-LEFT, :TOP-RIGHT, :BOTTOM-LEFT, :BOTTOM-RIGHT or :ROOT")

  (:method ((element t) (status t))
           (values nil)))


(defmethod insert-item ((tree quad-tree) (item quad-tree-node))
  (loop with key = (key tree)
     with y = (make-node-for-container tree nil)
     with classifier = (classifier tree)
     and x = (root tree)
     and key-item = (funcall key (element item))
     while (not (node-empty-p x))
     do
       (progn
         (setf y x)
         (case (funcall classifier key-item (funcall key (element x)))
           (:TOP-LEFT (setf x (top-left-child x)))
           (:TOP-RIGHT (setf x (top-right-child x)))
           (:BOTTOM-LEFT (setf x (bottom-left-child x)))
           (:BOTTOM-RIGHT (setf x (bottom-right-child x)))))

     finally (progn
               (cerror "continue" "classifier found ~a" classifier)
               (setf (parent item) y
                     (tree item) tree)
               (if (node-empty-p y)
                   (progn
                     (notify-element-of-child-status (element item) :ROOT)
                     (setf (root tree) item))
                   (case (funcall classifier key-item (funcall key (element y)))
                     (:TOP-LEFT
                      (notify-element-of-child-status (element item) :TOP-LEFT)
                      (setf (top-left-child y) item))
                     (:TOP-RIGHT
                      (notify-element-of-child-status (element item) :TOP-RIGHT)
                      (setf (top-right-child y) item))
                     (:BOTTOM-LEFT
                      (notify-element-of-child-status (element item) :BOTTOM-LEFT)
                      (setf (bottom-left-child y) item))
                     (:BOTTOM-RIGHT
                      (notify-element-of-child-status
                       (element item) :BOTTOM-RIGHT)
                      (setf (bottom-right-child y) item))))))
  (incf (size tree))
  (values tree))


(defmethod empty-p ((tree quad-tree))
  (node-empty-p (root tree)))

(defmethod empty! ((tree quad-tree))
  (setf (root tree) (make-node-for-container tree nil))
  (setf (size tree) 0)
  (values tree))


;; find-item needs to operate a bit differently -- it must find the
;; node in the tree that minimizes the test (e.g. minimal overlap);
;; therefore, it keeps searching until it finds a node that doesn't
;; pass the test of the container, and returns its parent.
(defmethod find-item ((tree quad-tree) (item quad-tree-node))
  (let ((last-node nil)
        (current (root tree))
        (test (test tree)))
    (loop with key = (key tree)
          with classifier = (classifier tree)
          and key-item = (funcall key (element item))
          while (and (not (node-empty-p current))
                     (funcall test
                              (element item) (element current))) do

          (setf last-node current)
          (case (funcall classifier key-item (funcall key (element current)))
            (:TOP-LEFT (setf current (top-left-child current)))
            (:TOP-RIGHT (setf current (top-right-child current)))
            (:BOTTOM-LEFT (setf current (bottom-left-child current)))
            (:BOTTOM-RIGHT (setf current (bottom-right-child current)))
            (otherwise (setf current nil))))

    (if (and (not (node-empty-p last-node))
             (funcall test (element item) (element last-node)))
      (values last-node)
      (values nil))))
