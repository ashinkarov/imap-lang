

eval: eval.ml
	ocamlc -pp "camlp4o pa_extend.cmo" -I +camlp4 -o $@ $<

clean:
	$(RM) eval.cmi eval.cmo
