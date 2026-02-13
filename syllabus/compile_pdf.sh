#!/bin/bash
cd /Users/jonathanwashburn/Projects/syllabus
/Library/TeX/texbin/pdflatex -interaction=nonstopmode RS_Publication_Order.tex > compile.log 2>&1
/Library/TeX/texbin/pdflatex -interaction=nonstopmode RS_Publication_Order.tex >> compile.log 2>&1
ls -la RS_Publication_Order.pdf >> compile.log 2>&1
