expr: mterm term;
term: mfactor factor;
factor: num 
      | var;
mterm: mterm term '+'
     | EMPTY;
mfactor: mfactor factor '*'
       | EMPTY;
	   
terminals
num: /\d+(\.\d+)?/;
var: /\w\S*/;