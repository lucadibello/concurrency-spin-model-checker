FROM mcr.microsoft.com/devcontainers/base:alpine-3.19 

# Avoid warnings by switching to noninteractive
ENV DEBIAN_FRONTEND=noninteractive

# Configure apt and install packages
RUN apk update \
	&& apk add --no-cache \
	bash \
	curl \
	git \
	sudo \
	wget \
	zsh \
	bison \
	&& rm -rf /var/lib/apt/lists/*

# Force oh-my-zsh install script to run in non-interactive mode
RUN rm -rf "/root/.oh-my-zsh" 
RUN sh -c "$(wget -O- https://raw.githubusercontent.com/ohmyzsh/ohmyzsh/master/tools/install.sh)"

# 1. zsh-autosuggestions
RUN git clone https://github.com/zsh-users/zsh-autosuggestions.git
RUN mv zsh-autosuggestions ~/.oh-my-zsh/custom/plugins/zsh-autosuggestions

# 2. zsh-syntax-highlighting
RUN git clone https://github.com/zsh-users/zsh-syntax-highlighting.git
RUN mv zsh-syntax-highlighting ~/.oh-my-zsh/custom/plugins/zsh-syntax-highlighting

# 3. zsh-completions
RUN git clone https://github.com/zsh-users/zsh-completions
RUN mv zsh-completions ~/.oh-my-zsh/custom/plugins/zsh-completions

# Add plugins to zshrc
RUN echo "plugins=(git zsh-autosuggestions zsh-syntax-highlighting zsh-completions)" >> /home/vscode/.zshrc

# Set the default shell to zsh
RUN chsh -s /bin/zsh vscode

# Clone + build Spin model checker
WORKDIR /home/vscode
RUN git clone https://github.com/nimble-code/Spin.git
WORKDIR /home/vscode/Spin
RUN make
RUN cp Src/spin /usr/local/bin

# Now, add Spin to the PATH
ENV PATH="/home/vscode/Spin:${PATH}"