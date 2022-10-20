FROM ubuntu:20.04

LABEL maintainer="Adam Scislowicz <adam.scislowicz@gmail.com>"

ENV UID=1000
ENV GID=1000
ARG USER
ARG ESP_IDF_TAG=release-v5.0

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

WORKDIR /tmp

RUN apt-get update \
    && apt-get install -y curl gnupg2 lsb-release software-properties-common \
    && curl -fsSL https://apt.releases.hashicorp.com/gpg | apt-key add - \
    && apt-add-repository "deb [arch=amd64] https://apt.releases.hashicorp.com $(lsb_release -cs) main" \
    && apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 93C4A3FD7BB9C367 \
    && apt-add-repository "deb http://ppa.launchpad.net/ansible/ansible/ubuntu focal main" \
    && curl -fsSL https://packages.cloud.google.com/apt/doc/apt-key.gpg | apt-key --keyring /usr/share/keyrings/cloud.google.gpg add - \
    && echo "deb [signed-by=/usr/share/keyrings/cloud.google.gpg] https://packages.cloud.google.com/apt cloud-sdk main" | tee -a /etc/apt/sources.list.d/google-cloud-sdk.list \
    && add-apt-repository ppa:kelleyk/emacs \
    && apt-get update \
    && apt-get upgrade -y \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    ansible \
    clangd \
    clang-format \
    cmake \
    debconf \
    dstat \
    emacs28-nativecomp \
    gcc-arm-none-eabi \
    git \
    google-cloud-cli \
    graphviz \
    htop \
    iproute2 \
    kubectl \
    libgraph-easy-perl \
    libnewlib-arm-none-eabi \
    locales \
    neovim \
    nftables \
    netfilter-persistent \
    ninja-build \
    openssh-server \
    openssl \
    pkg-config \
    procps \
    python3 \
    python3-pip \
    python3-venv \
    rsync \
    socat \
    strace \
    sudo \
    terraform \
    tmux \
    tshark \
    tzdata \
    unzip \
    wget \
    && sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen \
    && locale-gen \
    && terraform -install-autocomplete \
    && pip3 install --no-cache-dir awscli nox \
    && curl https://rclone.org/install.sh | bash \
    && curl https://github.com/mozilla/sops/releases/download/v3.6.1/sops_3.6.1_amd64.deb \
    -Lo sops_3.6.1_amd64.deb && \
    dpkg -i ./sops_3.6.1_amd64.deb \
    && curl -sL https://aka.ms/InstallAzureCLIDeb | bash \
    && groupadd -g $GID $USER \
    && useradd -l -g $USER -G sudo -u $UID -m $USER \
    && echo '%sudo ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

USER $USER
WORKDIR /home/$USER
ENV PICO_SDK_PATH=/home/$USER/pico/pico-sdk
ENV FREERTOS_KERNEL_PATH=/home/$USER/FreeRTOS/FreeRTOS/Source
ENV IDF_PATH=/opt/esp/idf
RUN curl https://raw.githubusercontent.com/raspberrypi/pico-setup/master/pico_setup.sh | SKIP_VSCODE=1 SKIP_UART=1 bash
COPY --from=espressif/idf:release-v5.0 /opt/esp /opt/esp
RUN $IDF_PATH/install.sh
RUN echo source $IDF_PATH/export.sh >> ~/.bashrc
