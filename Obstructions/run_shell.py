import subprocess, threading
import os, signal


class Command(object):
    def __init__(self, cmd):
        self.cmd = cmd
        self.process = None

        self.stdout = None
        self.stderr = None

    def run(self, timeout, hide_output=True):
        def target():
            if hide_output:
                self.process = subprocess.Popen(
                    self.cmd,
                    shell=True,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    preexec_fn=os.setsid,
                )
            else:
                self.process = subprocess.Popen(
                    self.cmd,
                    shell=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    preexec_fn=os.setsid,
                )
            self.stdout, self.stderr = self.process.communicate()

        thread = threading.Thread(target=target)
        thread.start()

        thread.join(timeout)
        if thread.is_alive():
            os.killpg(self.process.pid, signal.SIGTERM)
            thread.join()

        return self.process.returncode
