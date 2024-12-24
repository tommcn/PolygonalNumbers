FROM mcr.microsoft.com/devcontainers/base:debian-12

RUN apt-get update
RUN apt-get install -y texlive
RUN apt-get install -y graphviz graphviz-dev
RUN apt-get install -y python3 python3-dev python3-pip

ENV ELAN_HOME=/usr/local/elan \
    PATH=/usr/local/elan/bin:$PATH

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

RUN chmod -R a+w $ELAN_HOME

RUN apt-get install python3-pygraphviz
RUN pip install leanblueprint --break-system-packages
