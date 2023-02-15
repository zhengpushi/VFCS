# ===================================================================
# Copyright 2022 ZhengPu Shi
#  This file is part of VFCS. It is distributed under the MIT
#  "expat license". You should have recieved a LICENSE file with it.
# ===================================================================

HTMLDIR = ../../../html/FML4FCS/Introduction

html: index.tex
	htlatex index.tex
	sed -i s/"<title></title>"/"<title>FML4FCS - Introduction </title>"/ index.html
	sed -i s/"width=\"418\" height=\"418\""/"width=\"800\""/g index.html
	sed -i '12 a<script src="/FML4FCS/web-common/jquery-3.6.0.min.js"></script>' index.html
	sed -i '13 a<div id="header"></div><script type="text/javascript">$$("#header").load("/FML4FCS/web-common/header.html");</script>' index.html
	sed -i 's?</body></html>?<div id="footer"></div><script type="text/javascript">$$("#footer").load("/FML4FCS/web-common/footer.html");</script>\n</body></html>?' index.html
	mkdir -p $(HTMLDIR)
	mv -f index.html *.css *.png $(HTMLDIR)/ 2>/dev/null || :
	mkdir -p $(HTMLDIR)/figures
	cp -f figures/*.png $(HTMLDIR)/figures/ 2>/dev/null || :

clean:
	rm *.4ct *.4tc *.dvi *.idv *.lg *.log *.out *.gz *.tmp *.toc *.xref *.aux

