#
# Usage
# make     	  	自动编译所有 *.tex 文件到 *.pdf
# make clean  	清理临时文件，不包括 *.pdf
# make cleanall 清理临时文件，包括 *.pdf

pdfs := $(patsubst %.tex,%.pdf,$(wildcard *.tex))
all : $(pdfs)

bib=

%.pdf : %.tex
	pdflatex $< -o $@

clean:
	-rm *.toc *.out *.aux *.log *.nav *.snm *.gz *.vrb *.bbl *.blg *.spl

cleanall: clean
	rm *.pdf

.PHONY: clean
