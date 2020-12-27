expr: mterm term
	| EMPTY;
term: mfactor factor;
factor: num 
      | var
	  | expr;
mterm: mterm term '+'
     | EMPTY;
mfactor: mfactor factor '*'
       | EMPTY;
cheese: pei;
pei: cheese;
	   
terminals
num: /\d+(\.\d+)?/;
var: /\w\S*/;