;;; graph.el --- Graph theory library for Emacs

;; Copyright (C) 2023 Your Name

;; Author: Your Name <your.email@example.com>
;; Version: 1.0
;; Keywords: graph, graph-theory, algorithms, data structures
;; URL: https://example.com/graph.

;; This file is not part of GNU Emacs.

;;; Commentary:

;; This library provides a set of functions and data structures for working with
;; graphs in Emacs Lisp. It includes for creating graphs, adding vertices
;; and edges,d performing common graph operations such as traversal and searching.

;;; Code:

(require 'cl)

(cl-defstruct
    (graph-vertex
     (:constructor graph-make-vertex
                   (key &optional (data nil)))
     (:conc-name graph-vertex-)
     (:copier nil))
  key data)

(cl-defstruct
    (graph-edge
     (:constructor graph-make-edge (source target weight data))
     (:conc-name graph-edge-))
  source target weight data)

(cl-defstruct
    (graph (:constructor graph-make (&optional vertices edges directed))
           (:conc-name graph-))
  (vertices (make-hash-table :test #'equal))
  (edges nil)
  (directed nil))

(defun graph-add-vertex (graph key &optional data)
  "Add a vertex with KEY and DATA to GRAPH."
  (puthash key (graph-make-vertex key data)
           (graph-vertices graph)))

(defun graph-get-vertex (graph key)
  "Get the vertex with KEY from."
  (gethash key (graph- graph)))

(defun graph-add-edge (graph source target &optional weight data)
  "Add an edge from to TARGET with WEIGHT to GRAPH."
  (push (graph-make-edge source target weight data)
        (graph-edges graph))
  (unless (graph-directed graph)
    (push (graph-make-edge target source weight data)
          (graph-edges graph))))

(defun graph-get-neighbors (graph vertex)
  "Get the neighbors of VERTEX in GRAPH."
  (let (neighbors)
    (dolist (edge (graph-edges graph))
      (cond
       ((equal (graph-edge-source edge) vertex)
        (push (cons (graph-edge-target edge)
                    (graph-edge-weight edge))
              neighbors))
       ((and (not (graph-directed graph))
             (equal (graph-edge-target edge) vertex))
        (push (cons (graph-edge-source edge)
                    (graph-edge-weight edge))
              neighbors))))
    neighbors))

(defun graph-bfs (graph start-key)
  "Perform a breadth-first search on GRAPH starting from the vertex with START-KEY."
  (let ((queue (list (graph-get-vertex graph start-key)))
        (visited (make-hash-table :test #'equal))
        result)
    (while queue
      (let* ((current (pop queue))
             (key (graph-vertex-key current)))
        (unless (gethash key visited)
          (puthash key t visited)
          (push key result)
          (dolist (neighbor (graph-get-neighbors current))
            (push neighbor queue))))))
  (nreverse result))

(defun graph-adjacency-list (graph)
  (let (adjlist)
    (maphash (lambda (key data)
               (push (cons key (graph-get-neighbors graph key))
                     adjlist))
             (graph-vertices graph))
    adjlist))

(defun graph-shortest-path (graph start-node end-node)
  "Find shortest path from START-NODE to END-NODE using Dijkstra's algorithm.
GRAPH is an adjacency list representation of the graph, where
each element is of the form (node neighbors), and neighbors is a
list of `(neighbor-node . distance)' pairs.

Returns a list of nodes and their distance to the next node in
the list, from START-NODE to END-NODE.

  ((START-NODE . 300) (SOME-NODE . 100) (SOME-NODE . 200) (END-NODE . 0))"
  (let ((dist (make-hash-table :test #'equal))
        (prev (make-hash-table :test #'equal))
        (queue (make-heap #'(lambda (a b) (< (car a) (car b)))))
        (visited (make-hash-table :test #'equal))
        (adjlist (graph-adjacency-list graph)))
    ;; Initialize distances and previous nodes
    (mapc #'(lambda (entry)
              (puthash (car entry) most-positive-fixnum dist))
          adjlist)
    (puthash start-node 0 dist)
    ;; Initialize priority queue with start node
    (heap-add queue (cons 0 start-node))
    (catch 'completed
      (while (not (heap-empty queue))
        (let* ((current (heap-delete-root queue))
               (curr-node (cdr current))
               (curr-dist (car current)))
          (unless (gethash curr-node visited)
            (puthash curr-node t visited)
            (when (equal curr-node end-node)
              ;; Found shortest path, reconstruct path and return
              (let (path)
                (while curr-node
                  (let ((entry (if (consp curr-node)
                                   curr-node
                                 (cons curr-node 0))))
                    (push entry path)
                    (setq curr-node (gethash (car entry) prev))))
                (throw 'completed path)))
            ;; Process neighbors
            (dolist (neighbor (cdr (assoc curr-node adjlist)))
              (let* ((neighbor-node (car neighbor))
                     (neighbor-dist (cdr neighbor))
                     (new-dist (+ curr-dist neighbor-dist)))
                (when (< new-dist (gethash neighbor-node dist))
                  (puthash neighbor-node new-dist dist)
                  (puthash neighbor-node (cons curr-node neighbor-dist) prev)
                  (heap-add queue (cons new-dist neighbor-node)))))))))))

(let ((graph (graph-make)))
  (setf (graph-directed graph) t)
  (graph-add-vertex graph 'a)
  (graph-add-vertex graph 'b)
  (graph-add-vertex graph 'c)
  (graph-add-vertex graph 'd)
  (graph-add-vertex graph 'e)
  (graph-add-vertex graph 'f)
  (graph-add-edge graph 'a 'b 7)
  (graph-add-edge graph 'a 'c 9)
  (graph-add-edge graph 'a 'f 14)
  (graph-add-edge graph 'b 'c 10)
  (graph-add-edge graph 'b 'd 15)
  (graph-add-edge graph 'c 'd 11)
  (graph-add-edge graph 'c 'f 2)
  (graph-add-edge graph 'd 'e 6)
  (graph-add-edge graph 'e 'f 9)
  ;; (=> (a c d e) distance 26)
  (graph-shortest-path graph 'a 'e))

(provide 'graph)

;;; graph.el ends here
