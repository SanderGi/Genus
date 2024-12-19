const adjlist = document.getElementById("adjlist");
const calculate = document.getElementById("calculate");
const stderr = document.getElementById("stderr");
const stdout = document.getElementById("stdout");
const exampleSelect = document.getElementById("example_adj");
const loadExample = document.getElementById("load_example");

const serverorigin = location.origin;
const serverhost = location.host;

// regex to match `[ ] 0%` `[# ] 1%` `[## ] 2%` etc.
const progressRegex = /\[\s*#*\s*\]\s*\d+%/g;

calculate.onclick = () => {
  const adj = [];
  for (const line of adjlist.value.trim().split("\n")) {
    const neighbors = line
      .trim()
      .split(" ")
      .map((x) => parseInt(x));
    adj.push(neighbors);
    if (neighbors.some((x) => isNaN(x))) {
      alert("Invalid input");
      return;
    }
  }

  calculate.disabled = true;
  stderr.innerHTML = "";
  stdout.innerHTML = "";

  const socket = new WebSocket(
    `${
      location.protocol === "https:" ? "wss:" : "ws:"
    }//${serverhost}/stream_calc_genus`
  );

  let laststderr = "";
  let progress = "";
  socket.onmessage = async (event) => {
    const [type, data] = event.data.split(":", 2);

    if (type === "STDERR") {
      const line = data + "<br>";
      if (progressRegex.test(line)) {
        progress = line;
      } else {
        laststderr += line;
        if (progress !== "") {
          laststderr += progress + "<br>";
          progress = "";
        }
      }
      console.log(line, progressRegex.test(line)); // magic line that makes it work
      stderr.innerHTML = laststderr + "<br>" + progress;
    } else if (type === "STDOUT") {
      stdout.innerHTML += data + "<br>";
    }
  };

  socket.onopen = () => {
    socket.send(JSON.stringify(adj));
  };

  socket.onclose = () => {
    calculate.disabled = false;
  };
};

fetch(`${serverorigin}/adjacency_lists`).then(async (response) => {
  const examples = await response.json();
  for (const name of examples.sort()) {
    const option = document.createElement("option");
    option.value = name;
    option.text = name;
    exampleSelect.appendChild(option);
  }
});
loadExample.onclick = async () => {
  const response = await fetch(
    `${serverorigin}/adjacency_lists/${exampleSelect.value}`
  );
  adjlist.value = await response.text();
  // remove the first line
  adjlist.value = adjlist.value.replace(/^.+\n/, "");
  // remove 65536
  adjlist.value = adjlist.value.replace(/65536/g, "");
  // remove whitespace at the end of each line
  adjlist.value = adjlist.value.replace(/\s+$/gm, "");
};
