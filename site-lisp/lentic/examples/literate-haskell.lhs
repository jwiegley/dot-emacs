\begin{code}
tsort []     = []
tsort (x:xs) = tsort [y | y<-xs, y>x] ++ [x] ++ tsort [y | y<-xs, y<=x]
\end{code}

And this seems to be working just fine now

(oref lentic-config :this-buffer)
(oref lentic-config :that-buffer)

%% Local Variables:
%% lentic-init: lentic-haskell-latex-init
%% End:
