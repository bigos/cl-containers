(in-package #:containers)

;;; ------------------ my tests ------------------------------------------------

(declaim (optimize (debug 3)))

(defun test-exploration ()
  (let ((c (make-instance 'quad-tree)))
    (unless (eq (size c) 0)
      (cerror "wrong size ~a , but 0 expected" (size c)))
    (insert-item c (make-instance 'quad-tree-node))
    (format t "---------- ~A~%" (size c))
    ;; 1 works but 0 gives you a vector type problem
    ;; The value
    ;; 1
    ;; is not of type
    ;; (OR (VECTOR CHARACTER) (VECTOR NIL) BASE-STRING FUNCTION
    ;;     SYMBOL CONDITION SB-PCL::CONDITION-CLASS)
    (unless (= (size c) 0)
      (cerror "wrong size ~a , but 1 expected" (size c)))
    ;; (empty! c)
    ;; (unless (eq (size c) 0)
    ;;   (cerror "wrong size ~a , but 0 expected" (size c)))
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
