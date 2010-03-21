all: AlgorithmW AlgorithmW.pdf

AlgorithmW: AlgorithmW.lhs
	ghc --make AlgorithmW.lhs

AlgorithmW.pdf: AlgorithmW.tex
	latex AlgorithmW.tex
	pdflatex AlgorithmW.tex

AlgorithmW.tex: AlgorithmW.lhs
	lhs2TeX AlgorithmW.lhs > AlgorithmW.tex

clean:
	rm -f *tex *aux *log *out *ptb *~ *dvi *hi *o AlgorithmW
