// SPDX-FileCopyrightText: 2026 Alexander Metzger
// SPDX-License-Identifier: GPL-2.0-only

import * as THREE from "three";
import { OrbitControls } from "/vendor/OrbitControls.js";

const algorithm = document.getElementById("algorithm");
const outputFormat = document.getElementById("output_format");
const adjlist = document.getElementById("adjlist");
const calculate = document.getElementById("calculate");
const stderr = document.getElementById("stderr");
const stdout = document.getElementById("stdout");
const exampleSelect = document.getElementById("example_adj");
const loadExample = document.getElementById("load_example");
const runtime = document.getElementById("runtime");

const serverorigin = location.origin;
const serverhost = location.host;

// regex to match `[ ] 0%` `[# ] 1%` `[## ] 2%` etc.
const progressRegex = /\[\s*#*\s*\]\s*\d+%/g;
let activeViewer = null;

function setPanelContent(panel, content, isEmpty = false) {
  panel.innerHTML = content;
  panel.classList.toggle("empty-state", isEmpty);
}

function markPanelActive(panel) {
  panel.classList.remove("empty-state");
}

function clearOutput() {
  if (activeViewer) {
    activeViewer.dispose();
    activeViewer = null;
  }
  stdout.innerHTML = "";
  stdout.classList.remove("empty-state");
}

calculate.onclick = () => {
  const alg = algorithm.value;
  const format = outputFormat.value;
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
  setPanelContent(stderr, "Waiting for status...", true);
  clearOutput();
  setPanelContent(runtime, "Running...", true);

  const socket = new WebSocket(
    `${
      location.protocol === "https:" ? "wss:" : "ws:"
    }//${serverhost}/stream_calc_genus`,
  );

  let laststderr = "";
  let progress = "";
  socket.onmessage = async (event) => {
    const separator = event.data.indexOf(":");
    const type = separator === -1 ? event.data : event.data.slice(0, separator);
    const data = separator === -1 ? "" : event.data.slice(separator + 1);

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
      markPanelActive(stderr);
      stderr.innerHTML = laststderr + "<br>" + progress;
    } else if (type === "STDOUT") {
      markPanelActive(stdout);
      stdout.innerHTML += data + "<br>";
    } else if (type === "TIME") {
      markPanelActive(runtime);
      runtime.innerHTML = data;
    } else if (type === "JSON") {
      clearOutput();
      const pre = document.createElement("pre");
      try {
        pre.textContent = JSON.stringify(JSON.parse(data), null, 2);
      } catch {
        pre.textContent = data;
      }
      markPanelActive(stdout);
      stdout.appendChild(pre);
    } else if (type === "IMAGE") {
      clearOutput();
      const image = document.createElement("img");
      image.src = data;
      image.alt = "Graph embedding drawing";
      image.className = "embedding-image";
      markPanelActive(stdout);
      stdout.appendChild(image);
    } else if (type === "MODEL") {
      clearOutput();
      try {
        markPanelActive(stdout);
        renderModel(JSON.parse(data), stdout);
      } catch (error) {
        const pre = document.createElement("pre");
        pre.textContent = error.stack || error.message || String(error);
        markPanelActive(stdout);
        stdout.appendChild(pre);
      }
    }
  };

  socket.onopen = () => {
    socket.send(JSON.stringify({ adj, alg, outputFormat: format }));
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
    `${serverorigin}/adjacency_lists/${exampleSelect.value}`,
  );
  adjlist.value = await response.text();
  // remove the first line
  adjlist.value = adjlist.value.replace(/^.+\n/, "");
  // remove 65535
  adjlist.value = adjlist.value.replace(/65535/g, "");
  // remove whitespace at the end of each line
  adjlist.value = adjlist.value.replace(/\s+$/gm, "");
};

function parseObj(objText) {
  const vertices = [[0, 0, 0]];
  const uvs = [[0, 0]];
  const positions = [];
  const texcoords = [];
  const indices = [];
  const graphLines = [];
  const graphPoints = [];
  const graphPointLabels = new Map();
  const cornerIndices = new Map();

  const addCorner = (token) => {
    const [vertexToken, textureToken] = token.split("/");
    const vertexIndex = parseInt(vertexToken, 10);
    const textureIndex = textureToken ? parseInt(textureToken, 10) : 0;
    const key = `${vertexIndex}/${textureIndex}`;
    let index = cornerIndices.get(key);
    if (index !== undefined) return index;

    const vertex = vertices[vertexIndex];
    const uv = uvs[textureIndex] || [0, 0];
    index = positions.length / 3;
    positions.push(vertex[0], vertex[1], vertex[2]);
    texcoords.push(uv[0], uv[1]);
    cornerIndices.set(key, index);
    return index;
  };

  for (const rawLine of objText.split(/\r?\n/)) {
    const line = rawLine.trim();
    if (line.startsWith("# graph_vertex_label ")) {
      const parts = line.split(/\s+/);
      const vertexIndex = parseInt(parts[2], 10);
      const label = parts[3];
      const labelPosition =
        parts.length >= 7 ? parts.slice(4, 7).map(Number) : null;
      if (!Number.isNaN(vertexIndex) && label) {
        graphPointLabels.set(vertexIndex, {
          label,
          labelPosition:
            labelPosition && labelPosition.every(Number.isFinite)
              ? labelPosition
              : null,
        });
      }
      continue;
    }
    if (line === "" || line.startsWith("#")) continue;
    const parts = line.split(/\s+/);

    if (parts[0] === "v") {
      vertices.push(parts.slice(1, 4).map(Number));
    } else if (parts[0] === "vt") {
      uvs.push(parts.slice(1, 3).map(Number));
    } else if (parts[0] === "f") {
      const face = parts.slice(1).map(addCorner);
      for (let i = 1; i < face.length - 1; i++) {
        indices.push(face[0], face[i], face[i + 1]);
      }
    } else if (parts[0] === "l") {
      const line = parts
        .slice(1)
        .map((token) => vertices[parseInt(token.split("/")[0], 10)])
        .filter(Boolean);
      if (line.length >= 2) graphLines.push(line);
    } else if (parts[0] === "p") {
      for (const token of parts.slice(1)) {
        const vertexIndex = parseInt(token.split("/")[0], 10);
        const point = vertices[vertexIndex];
        const labelInfo = graphPointLabels.get(vertexIndex);
        if (point) {
          graphPoints.push({
            position: point,
            label: labelInfo?.label || String(graphPoints.length + 1),
            labelPosition: labelInfo?.labelPosition || null,
          });
        }
      }
    }
  }

  const geometry = new THREE.BufferGeometry();
  geometry.setAttribute(
    "position",
    new THREE.Float32BufferAttribute(positions, 3),
  );
  geometry.setAttribute("uv", new THREE.Float32BufferAttribute(texcoords, 2));
  geometry.setIndex(indices);
  geometry.computeVertexNormals();
  geometry.normalizeNormals();
  geometry.computeBoundingSphere();
  return { geometry, graphLines, graphPoints };
}

function makeTextSprite(text, size) {
  const canvas = document.createElement("canvas");
  const context = canvas.getContext("2d");
  const fontSize = 44;
  const padding = 14;
  const label = String(text);
  context.font = `700 ${fontSize}px system-ui, -apple-system, sans-serif`;
  const metrics = context.measureText(label);
  canvas.width = Math.ceil(metrics.width + padding * 2);
  canvas.height = fontSize + padding * 2;

  context.font = `700 ${fontSize}px system-ui, -apple-system, sans-serif`;
  context.textBaseline = "middle";
  context.lineJoin = "round";
  context.lineWidth = 8;
  context.strokeStyle = "rgba(247, 247, 244, 0.96)";
  context.fillStyle = "#111111";
  context.strokeText(label, padding, canvas.height / 2);
  context.fillText(label, padding, canvas.height / 2);

  const texture = new THREE.CanvasTexture(canvas);
  texture.colorSpace = THREE.SRGBColorSpace;
  const material = new THREE.SpriteMaterial({
    map: texture,
    transparent: true,
    depthTest: true,
    depthWrite: false,
  });
  const sprite = new THREE.Sprite(material);
  const aspect = canvas.width / canvas.height;
  sprite.scale.set(size * aspect, size, 1);
  sprite.renderOrder = 10;
  sprite.userData.dispose = () => {
    texture.dispose();
    material.dispose();
  };
  return sprite;
}

function makeGraphOverlay(graphLines, graphPoints, center, radius) {
  const group = new THREE.Group();
  const strokeRadius = Math.max(radius * 0.0016, 0.0025);
  const labelScale = Math.max(radius * 0.075, 0.1);
  const labelOffset = Math.max(radius * 0.012, strokeRadius * 3);
  const strokeMaterial = new THREE.MeshBasicMaterial({
    color: 0x111111,
    depthTest: true,
    depthWrite: false,
    polygonOffset: true,
    polygonOffsetFactor: -2,
    polygonOffsetUnits: -2,
  });
  const pointMaterial = new THREE.MeshBasicMaterial({
    color: 0xf3f3f0,
    depthTest: true,
    depthWrite: false,
    polygonOffset: true,
    polygonOffsetFactor: -2,
    polygonOffsetUnits: -2,
  });

  const capPoints = [];
  for (const line of graphLines) {
    const points = line.map(
      ([x, y, z]) =>
        new THREE.Vector3(x - center.x, y - center.y, z - center.z),
    );
    if (points.length > 0) {
      capPoints.push(points[0], points[points.length - 1]);
    }
    const path = new THREE.CurvePath();
    for (let i = 0; i < points.length - 1; i++) {
      path.add(new THREE.LineCurve3(points[i], points[i + 1]));
    }
    const tube = new THREE.TubeGeometry(
      path,
      Math.max(6, Math.min(2048, points.length - 1)),
      strokeRadius,
      5,
      false,
    );
    group.add(new THREE.Mesh(tube, strokeMaterial));
  }

  if (capPoints.length > 0) {
    const capGeometry = new THREE.SphereGeometry(strokeRadius * 1.08, 8, 6);
    const capMesh = new THREE.InstancedMesh(
      capGeometry,
      strokeMaterial,
      capPoints.length,
    );
    const matrix = new THREE.Matrix4();
    capPoints.forEach((point, index) => {
      matrix.setPosition(point);
      capMesh.setMatrixAt(index, matrix);
    });
    capMesh.instanceMatrix.needsUpdate = true;
    group.add(capMesh);
  }

  if (graphPoints.length > 0) {
    const pointGeometry = new THREE.SphereGeometry(strokeRadius * 1.25, 12, 8);
    const pointMesh = new THREE.InstancedMesh(
      pointGeometry,
      pointMaterial,
      graphPoints.length,
    );
    const matrix = new THREE.Matrix4();
    graphPoints.forEach(({ position: [x, y, z] }, index) => {
      matrix.setPosition(x - center.x, y - center.y, z - center.z);
      pointMesh.setMatrixAt(index, matrix);
    });
    pointMesh.instanceMatrix.needsUpdate = true;
    group.add(pointMesh);

    graphPoints.forEach(({ position: [x, y, z], label, labelPosition }) => {
      const position = labelPosition
        ? new THREE.Vector3(
            labelPosition[0] - center.x,
            labelPosition[1] - center.y,
            labelPosition[2] - center.z,
          )
        : new THREE.Vector3(x - center.x, y - center.y, z - center.z);
      const sprite = makeTextSprite(label, labelScale);
      if (labelPosition) {
        sprite.position.copy(position);
      } else {
        const normal =
          position.lengthSq() > 1e-10
            ? position.clone().normalize()
            : new THREE.Vector3(0, 0, 1);
        sprite.position.copy(position.addScaledVector(normal, labelOffset));
      }
      group.add(sprite);
    });
  }

  group.userData.dispose = () => {
    group.traverse((child) => {
      if (child.geometry) child.geometry.dispose();
      if (child !== group && child.userData?.dispose) child.userData.dispose();
    });
    strokeMaterial.dispose();
    pointMaterial.dispose();
  };
  return group;
}

function renderModel(model, container) {
  if (activeViewer) {
    activeViewer.dispose();
    activeViewer = null;
  }

  const viewer = document.createElement("div");
  viewer.className = "model-viewer";
  container.appendChild(viewer);

  const renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.setSize(viewer.clientWidth, viewer.clientHeight);
  renderer.outputColorSpace = THREE.SRGBColorSpace;
  viewer.appendChild(renderer.domElement);

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0xf7f7f4);

  const camera = new THREE.PerspectiveCamera(
    45,
    viewer.clientWidth / viewer.clientHeight,
    0.01,
    1000,
  );
  camera.position.set(0, -7, 4);

  const controls = new OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true;

  const parsedObj = parseObj(model.obj);
  const { geometry, graphLines, graphPoints } = parsedObj;
  geometry.computeBoundingBox();
  const center = new THREE.Vector3();
  geometry.boundingBox.getCenter(center);
  geometry.translate(-center.x, -center.y, -center.z);
  geometry.computeBoundingSphere();

  const radius = geometry.boundingSphere?.radius || 1;
  if (model.genus === 0 && graphPoints.length > 0) {
    const graphCenter = new THREE.Vector3();
    graphPoints.forEach(({ position: [x, y, z] }) => {
      graphCenter.add(
        new THREE.Vector3(x - center.x, y - center.y, z - center.z),
      );
    });
    graphCenter.multiplyScalar(1 / graphPoints.length);
    if (graphCenter.lengthSq() > 1e-10) {
      graphCenter.normalize();
      camera.position.copy(graphCenter.multiplyScalar(radius * 3.2));
    } else {
      camera.position.set(0, -radius * 2.6, radius * 1.3);
    }
  } else {
    camera.position.set(0, -radius * 2.6, radius * 1.3);
  }
  camera.near = Math.max(0.01, radius / 100);
  camera.far = radius * 20;
  camera.updateProjectionMatrix();
  controls.target.set(0, 0, 0);
  controls.update();

  const material = new THREE.MeshStandardMaterial({
    color: 0xc8cac7,
    side: THREE.DoubleSide,
    roughness: 0.66,
    metalness: 0.02,
  });
  const mesh = new THREE.Mesh(geometry, material);
  scene.add(mesh);
  const graphOverlay = makeGraphOverlay(
    graphLines,
    graphPoints,
    center,
    radius,
  );
  scene.add(graphOverlay);

  scene.add(new THREE.HemisphereLight(0xffffff, 0x777777, 2.2));
  const key = new THREE.DirectionalLight(0xffffff, 1.8);
  key.position.set(4, -5, 7);
  scene.add(key);

  const resizeObserver = new ResizeObserver(() => {
    const width = viewer.clientWidth;
    const height = viewer.clientHeight;
    if (!width || !height) return;
    renderer.setSize(width, height);
    camera.aspect = width / height;
    camera.updateProjectionMatrix();
  });
  resizeObserver.observe(viewer);

  let running = true;
  const animate = () => {
    if (!running) return;
    controls.update();
    renderer.render(scene, camera);
    requestAnimationFrame(animate);
  };
  animate();

  activeViewer = {
    dispose() {
      running = false;
      resizeObserver.disconnect();
      controls.dispose();
      geometry.dispose();
      material.dispose();
      graphOverlay.userData.dispose();
      renderer.dispose();
      viewer.remove();
    },
  };
}

function setBibtex(algorithm, output_format) {
  const page_bibtex = `@article{Metzger_2026,
    title={An efficient genus algorithm based on graph rotations},
    number={12}, volume={349}, ISSN={0012-365X},
    url={http://doi.org/10.1016/j.disc.2026.115308},
    DOI={10.1016/j.disc.2026.115308},
    journal={Discrete Mathematics},
    publisher={Elsevier BV},
    author={Metzger, Alexander and Ulrigg, Austin},
    year={2026}, month=Dec, pages={115308}
}`;
  const multi_genus_bibtex = `@article{article,
    title = {A practical algorithm for the computation of the genus},
    author = {Brinkmann, Gunnar},
    year = {2022}, month = {07},
    pages = {#P4.01}, volume = {22},
    journal = {Ars Mathematica Contemporanea},
    doi = {10.26493/1855-3974.2320.c2d}
}`;
  const planar_draw_bibtex = `@misc{brinkmann2025drawingmapsorientedsurfaces,
    title={Drawing maps on oriented surfaces}, 
    author={Gunnar Brinkmann},
    year={2025},
    eprint={2505.01480},
    archivePrefix={arXiv},
    primaryClass={cs.CG},
    url={https://arxiv.org/abs/2505.01480}, 
}`;
  let bibtex = "";
  if (algorithm === "multi_genus") {
    bibtex += multi_genus_bibtex + "\n";
  }
  bibtex += page_bibtex;
  if (["drawing", "3d"].includes(output_format)) {
    bibtex += "\n" + planar_draw_bibtex;
  }
  document.getElementById("bibtex-content").innerText = bibtex;
}

algorithm.addEventListener("change", () => {
  setBibtex(algorithm.value, outputFormat.value);
});

outputFormat.addEventListener("change", () => {
  setBibtex(algorithm.value, outputFormat.value);
});
