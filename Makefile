all:
	happy -gca ParExp.y
	alex -g LexExp.x
	ghc --make TestExp.hs -o TestExp

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocExp.* LexExp.* ParExp.* LayoutExp.* SkelExp.* PrintExp.* TestExp.* AbsExp.* TestExp ErrM.* SharedString.* ComposOp.* Exp.dtd XMLExp.* Makefile*
	

