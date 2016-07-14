How to use dReal in Windows using Docker
-----------------------------------------

 1. Install [Docker for Windows (for Windows 10)](https://docs.docker.com/docker-for-windows/) or [Docker Toolbox (for Windows 7/8)](https://www.docker.com/products/docker-toolbox). 
    Read [this](https://docs.docker.com/engine/installation/windows) for details. 
 2. Open Docker Quickstart Terminal (under Start Menu -> Docker Folder).
 3. Run `docker pull dreal/dreal3` to install the latest version of dReal.
 4. Run `docker run --rm dreal/dreal3 dReal --version` to check it's properly installed.
 5. We need to provide a way to pass a file in a Windows file system to dReal which is running inside of a VM (virtual machine). 
    - Consider an examplary scenario where we have a project directory `/c/Users/soonhok/project_dir`
      and there is `test.smt2` file in the directory.
    - Run `docker run --rm -v /c/Users/soonhok/project_dir:/tmp dreal/dreal3 dReal /tmp/test.smt2`
    - The above command mounts `/c/Users/soonhok/project_dir` directory as `/tmp` inside of a VM. 
      Then it executes `dReal /tmp/test.smt2` inside of the VM.
