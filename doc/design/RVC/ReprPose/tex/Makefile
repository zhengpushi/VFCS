#
# Usage
# make     	  	自动编译所有 *.tex 文件到 *.pdf，不带 bib
# make bib=1  	自动编译所有 *.tex 文件到 *.pdf，带 bib
# make clean  	清理临时文件，不包括 *.pdf
# make cleanall 清理临时文件，包括 *.pdf

pdfs := $(patsubst %.tex,%.pdf,$(wildcard *.tex))
all : $(pdfs)

bib=

ifdef bib 
%.pdf : %.tex
	pdflatex $< -o $@
	bibtex $(basename $<)
	pdflatex $< -o $@
	pdflatex $< -o $@
else
%.pdf : %.tex
	# pdflatex $< -o $@
	xelatex $< -o $@
endif

clean:
	-rm *.toc *.out *.aux *.log *.nav *.snm *.gz *.vrb *.bbl *.blg *.spl

view: *.pdf
	open *.pdf

%.docx : %.tex
	pandoc -s $< -o $@

docx: *.docx

cleanall: clean
	rm *.pdf

.PHONY: clean
