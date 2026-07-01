import * as THREE from "three";
import { OrbitControls } from "/vendor/OrbitControls.js";

const K33_BASE = [
  [3, 4, 5],
  [3, 4, 5],
  [3, 4, 5],
  [0, 1, 2],
  [0, 1, 2],
  [0, 1, 2],
];
const EDGES = [];
for (let left = 0; left < 3; left++) {
  for (let right = 3; right < 6; right++) EDGES.push([left, right]);
}
const REPRESENTATIVES = [
  {
    mask: 1,
    orbit: [
      1, 2, 3, 4, 5, 6, 8, 15, 16, 23, 24, 31,
      32, 39, 40, 47, 48, 55, 57, 58, 59, 60, 61, 62,
    ],
  },
];

const el = {
  viewer: document.getElementById("viewer"),
  representative: document.getElementById("representative_select"),
  orbitSummary: document.getElementById("orbit_summary"),
  rotationSystem: document.getElementById("rotation_system"),
  loadSurface: document.getElementById("load_surface"),
  toggleOriginal: document.getElementById("toggle_original"),
  status: document.getElementById("status"),
  verifyOrientation: document.getElementById("verify_orientation"),
  verifyResult: document.getElementById("verify_result"),
  vertexButtons: document.getElementById("vertex_buttons"),
  edgeSelect: document.getElementById("edge_select"),
  undoPoint: document.getElementById("undo_point"),
  clearEdge: document.getElementById("clear_edge"),
  smoothEdge: document.getElementById("smooth_edge"),
  saveLayout: document.getElementById("save_layout"),
  copyLayout: document.getElementById("copy_layout"),
  layoutJson: document.getElementById("layout_json"),
  applyLayout: document.getElementById("apply_layout"),
};

const state = {
  mode: "vertex",
  selectedVertex: 0,
  selectedEdge: edgeKey(0, 3),
  surfaceMesh: null,
  surfaceGroup: new THREE.Group(),
  originalGroup: new THREE.Group(),
  manualGroup: new THREE.Group(),
  vertexPositions: new Map(),
  edgeRoutes: new Map(),
  surfaceTriangles: [],
  center: new THREE.Vector3(),
  radius: 1,
  showOriginal: false,
};

const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
renderer.outputColorSpace = THREE.SRGBColorSpace;
el.viewer.appendChild(renderer.domElement);

const scene = new THREE.Scene();
scene.background = new THREE.Color(0xf7f7f3);
const camera = new THREE.PerspectiveCamera(45, 1, 0.01, 1000);
camera.position.set(0, -5, 2.8);
const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true;
scene.add(new THREE.HemisphereLight(0xffffff, 0x777777, 2.25));
const key = new THREE.DirectionalLight(0xffffff, 1.75);
key.position.set(4, -5, 7);
scene.add(key);
scene.add(state.surfaceGroup, state.originalGroup, state.manualGroup);

const raycaster = new THREE.Raycaster();
const pointer = new THREE.Vector2();
const triangleScratch = {
  ab: new THREE.Vector3(),
  ac: new THREE.Vector3(),
  ap: new THREE.Vector3(),
  bp: new THREE.Vector3(),
  cp: new THREE.Vector3(),
  bc: new THREE.Vector3(),
};
const resizeObserver = new ResizeObserver(resize);
resizeObserver.observe(el.viewer);
resize();
initControls();
animate();
loadSurface();

function initControls() {
  el.orbitSummary.textContent = "Verified: all 24 genus-2 systems are one symmetry class.";
  REPRESENTATIVES.forEach((rep, index) => {
    const option = document.createElement("option");
    option.value = String(index);
    option.textContent = `Representative mask ${rep.mask}, orbit size ${rep.orbit.length}`;
    el.representative.appendChild(option);
  });
  el.representative.addEventListener("change", renderRotationSystem);
  renderRotationSystem();
  for (let vertex = 0; vertex < 6; vertex++) {
    const button = document.createElement("button");
    button.type = "button";
    button.textContent = String(vertex);
    button.addEventListener("click", () => selectVertex(vertex));
    el.vertexButtons.appendChild(button);
  }
  for (const [a, b] of EDGES) {
    const option = document.createElement("option");
    option.value = edgeKey(a, b);
    option.textContent = `${a}-${b}`;
    el.edgeSelect.appendChild(option);
  }
  el.edgeSelect.addEventListener("change", () => {
    state.selectedEdge = el.edgeSelect.value;
    state.mode = "edge";
    updateActiveControls();
  });
  el.loadSurface.addEventListener("click", loadSurface);
  el.toggleOriginal.addEventListener("click", () => {
    state.showOriginal = !state.showOriginal;
    state.originalGroup.visible = state.showOriginal;
    el.toggleOriginal.classList.toggle("active", state.showOriginal);
  });
  el.undoPoint.addEventListener("click", () => {
    const route = state.edgeRoutes.get(state.selectedEdge) || [];
    route.pop();
    state.edgeRoutes.set(state.selectedEdge, route);
    drawManualOverlay();
  });
  el.clearEdge.addEventListener("click", () => {
    state.edgeRoutes.set(state.selectedEdge, []);
    drawManualOverlay();
  });
  el.smoothEdge.addEventListener("click", smoothSelectedEdge);
  el.verifyOrientation.addEventListener("click", verifyOrientations);
  el.saveLayout.addEventListener("click", saveLayout);
  el.copyLayout.addEventListener("click", copyLayout);
  el.applyLayout.addEventListener("click", applyLayout);
  renderer.domElement.addEventListener("pointerdown", onPointerDown);
  selectVertex(0);
}

function selectVertex(vertex) {
  state.mode = "vertex";
  state.selectedVertex = vertex;
  updateActiveControls();
}

function updateActiveControls() {
  [...el.vertexButtons.children].forEach((button, index) => {
    button.classList.toggle("active", state.mode === "vertex" && index === state.selectedVertex);
  });
}

function renderRotationSystem() {
  const rotation = currentRotation();
  el.rotationSystem.replaceChildren();
  rotation.forEach((neighbors, vertex) => {
    const row = document.createElement("div");
    row.className = "rotation-row";
    row.textContent = `${vertex}: (${neighbors.join(", ")})`;
    el.rotationSystem.appendChild(row);
  });
  el.verifyResult.textContent = "";
  el.verifyResult.className = "verify-result";
}

async function loadSurface() {
  const rep = REPRESENTATIVES[Number(el.representative.value || 0)];
  setStatus(`Loading genus-2 surface for mask ${rep.mask}...`);
  clearGroup(state.surfaceGroup);
  clearGroup(state.originalGroup);
  clearGroup(state.manualGroup);
  state.surfaceMesh = null;
  state.vertexPositions = new Map();
  state.edgeRoutes = new Map();
  state.surfaceTriangles = [];
  try {
    const model = await requestModel(rotationFromMask(rep.mask));
    buildSceneFromObj(model.obj);
    loadSavedLayout();
    drawManualOverlay();
    setStatus("Loaded the genus-2 representative. Click a vertex or route point onto the surface.");
  } catch (error) {
    setStatus(error.message);
  }
}

function requestModel(rotation) {
  return new Promise((resolve, reject) => {
    const socket = new WebSocket(`${location.protocol === "https:" ? "wss:" : "ws:"}//${location.host}/stream_calc_genus`);
    let done = false;
    socket.onopen = () => {
      socket.send(JSON.stringify({ alg: "none", outputFormat: "3d_raw", adj: rotation }));
    };
    socket.onmessage = (event) => {
      const separator = event.data.indexOf(":");
      const type = separator === -1 ? event.data : event.data.slice(0, separator);
      const data = separator === -1 ? "" : event.data.slice(separator + 1);
      if (type === "MODEL") {
        done = true;
        resolve(JSON.parse(data));
        socket.close();
      } else if (type === "JSON") {
        const parsed = JSON.parse(data);
        if (parsed.error) {
          done = true;
          reject(new Error(parsed.error));
          socket.close();
        }
      } else if (type === "STDERR") {
        setStatus(data);
      }
    };
    socket.onerror = () => {
      if (!done) reject(new Error("Could not load the genus-2 model"));
    };
    socket.onclose = () => {
      if (!done) reject(new Error("3D model request closed before a model was returned"));
    };
  });
}

function buildSceneFromObj(objText) {
  const parsed = parseObj(objText);
  parsed.geometry.computeBoundingBox();
  parsed.geometry.boundingBox.getCenter(state.center);
  parsed.geometry.translate(-state.center.x, -state.center.y, -state.center.z);
  parsed.geometry.computeBoundingSphere();
  state.radius = parsed.geometry.boundingSphere?.radius || 1;
  state.surfaceTriangles = buildSurfaceTriangles(parsed.geometry);

  const surface = new THREE.Mesh(
    parsed.geometry,
    new THREE.MeshStandardMaterial({
      color: 0xc8cac7,
      roughness: 0.66,
      metalness: 0.02,
      side: THREE.DoubleSide,
    }),
  );
  state.surfaceMesh = surface;
  state.surfaceGroup.add(surface);

  const originalMaterial = new THREE.MeshBasicMaterial({
    color: 0x111111,
    transparent: true,
    opacity: 0.22,
    depthTest: true,
    depthWrite: false,
  });
  const originalRadius = Math.max(state.radius * 0.0016, 0.0025);
  for (const line of parsed.graphLines) {
    const points = line.points.map((point) => point.clone().sub(state.center));
    state.originalGroup.add(makeTube(points, originalRadius, originalMaterial, Math.max(6, points.length - 1)));
  }
  state.originalGroup.visible = state.showOriginal;

  camera.position.set(0, -state.radius * 2.7, state.radius * 1.35);
  camera.near = Math.max(0.01, state.radius / 100);
  camera.far = state.radius * 20;
  camera.updateProjectionMatrix();
  controls.target.set(0, 0, 0);
  controls.update();
}

function onPointerDown(event) {
  if (!state.surfaceMesh) return;
  const rect = renderer.domElement.getBoundingClientRect();
  pointer.x = ((event.clientX - rect.left) / rect.width) * 2 - 1;
  pointer.y = -((event.clientY - rect.top) / rect.height) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  const hit = raycaster.intersectObject(state.surfaceMesh, false)[0];
  if (!hit) return;
  const point = hit.point.clone();
  if (state.mode === "vertex") {
    state.vertexPositions.set(state.selectedVertex, point);
    setStatus(`Placed vertex ${state.selectedVertex}.`);
  } else {
    const route = state.edgeRoutes.get(state.selectedEdge) || [];
    route.push(point);
    state.edgeRoutes.set(state.selectedEdge, route);
    setStatus(`Added route point ${route.length} for edge ${state.selectedEdge}.`);
  }
  drawManualOverlay();
}

function drawManualOverlay() {
  clearGroup(state.manualGroup);
  const vertexMaterial = new THREE.MeshBasicMaterial({
    color: 0xf5f5f0,
    depthTest: true,
    depthWrite: true,
  });
  const vertexRingMaterial = new THREE.MeshBasicMaterial({
    color: 0x111111,
    depthTest: true,
    depthWrite: true,
  });
  const routeMaterial = new THREE.MeshBasicMaterial({
    color: 0x0867d8,
    depthTest: true,
    depthWrite: true,
  });
  const vertexRadius = Math.max(state.radius * 0.018, 0.03);
  const routeRadius = Math.max(state.radius * 0.006, 0.01);

  for (const [vertex, position] of state.vertexPositions.entries()) {
    const dot = new THREE.Mesh(new THREE.SphereGeometry(vertexRadius, 18, 12), vertexMaterial);
    dot.position.copy(position);
    state.manualGroup.add(dot);
    const ring = new THREE.Mesh(new THREE.SphereGeometry(vertexRadius * 1.08, 18, 12), vertexRingMaterial);
    ring.material.side = THREE.BackSide;
    ring.position.copy(position);
    state.manualGroup.add(ring);
    const label = makeTextSprite(String(vertex), vertexRadius * 4.2);
    label.position.copy(position).addScaledVector(normalAtPoint(position), vertexRadius * 2.4);
    state.manualGroup.add(label);
  }

  for (const [a, b] of EDGES) {
    const start = state.vertexPositions.get(a);
    const end = state.vertexPositions.get(b);
    const controls = state.edgeRoutes.get(edgeKey(a, b)) || [];
    if (!start || !end) continue;
    const points = [start, ...controls, end].map((point) => point.clone());
    state.manualGroup.add(makeTube(points, routeRadius, routeMaterial, Math.max(8, points.length * 16)));
  }

  state.manualGroup.userData.dispose = () => {
    vertexMaterial.dispose();
    vertexRingMaterial.dispose();
    routeMaterial.dispose();
  };
}

function smoothSelectedEdge() {
  const [a, b] = state.selectedEdge.split("-").map(Number);
  const start = state.vertexPositions.get(a);
  const end = state.vertexPositions.get(b);
  if (!start || !end) {
    setStatus(`Place both endpoints for edge ${state.selectedEdge} before smoothing.`);
    return;
  }
  if (state.surfaceTriangles.length === 0) {
    setStatus("Load the surface before smoothing an edge.");
    return;
  }

  const controls = state.edgeRoutes.get(state.selectedEdge) || [];
  const basePoints = [start, ...controls, end].map((point) => point.clone());
  const controlLength = polylineLength(basePoints);
  if (controlLength < 1e-8) {
    setStatus(`Edge ${state.selectedEdge} is too short to smooth.`);
    return;
  }

  const curve = new THREE.CatmullRomCurve3(basePoints, false, "centripetal", 0.35);
  const sampleCount = Math.min(80, Math.max(18, Math.ceil(controlLength / Math.max(state.radius * 0.08, 0.04))));
  const projected = [];
  for (let i = 1; i < sampleCount; i++) {
    const sample = curve.getPoint(i / sampleCount);
    projected.push(projectToSurface(sample).point);
  }
  state.edgeRoutes.set(state.selectedEdge, projected);
  drawManualOverlay();
  setStatus(`Smoothed and projected ${state.selectedEdge} into ${projected.length + 2} surface samples.`);
}

function verifyOrientations() {
  const rotation = currentRotation();
  const missing = [];
  const reversed = [];
  const mismatches = [];
  for (let vertex = 0; vertex < rotation.length; vertex++) {
    const placed = state.vertexPositions.get(vertex);
    if (!placed) {
      missing.push(`vertex ${vertex}`);
      continue;
    }
    const exits = [];
    for (const neighbor of rotation[vertex]) {
      const exit = exitPointFor(vertex, neighbor);
      if (!exit) {
        missing.push(`edge ${edgeKey(vertex, neighbor)} near ${vertex}`);
        continue;
      }
      exits.push({ neighbor, point: exit });
    }
    if (exits.length !== rotation[vertex].length) continue;

    const normal = normalAtPoint(placed);
    const frame = tangentFrame(normal);
    const actual = exits
      .map(({ neighbor, point }) => {
        const tangentVector = point.clone().sub(placed);
        tangentVector.addScaledVector(normal, -tangentVector.dot(normal));
        return {
          neighbor,
          angle: Math.atan2(tangentVector.dot(frame.bitangent), tangentVector.dot(frame.tangent)),
          lengthSq: tangentVector.lengthSq(),
        };
      })
      .filter((item) => item.lengthSq > 1e-10)
      .sort((a, b) => a.angle - b.angle)
      .map((item) => item.neighbor);

    if (actual.length !== rotation[vertex].length) {
      missing.push(`distinct exits at ${vertex}`);
    } else if (cyclicOrderEqual(actual, rotation[vertex])) {
      continue;
    } else if (cyclicOrderEqual([...actual].reverse(), rotation[vertex])) {
      reversed.push(`${vertex}: (${actual.join(", ")})`);
    } else {
      mismatches.push(`${vertex}: got (${actual.join(", ")}), expected (${rotation[vertex].join(", ")})`);
    }
  }

  const problems = [];
  if (missing.length) problems.push(`Missing: ${missing.join("; ")}.`);
  if (reversed.length) problems.push(`Reversed orientation: ${reversed.join("; ")}.`);
  if (mismatches.length) problems.push(`Mismatched order: ${mismatches.join("; ")}.`);
  if (problems.length === 0) {
    el.verifyResult.textContent = "All placed edge exits match the representative cyclic order.";
    el.verifyResult.className = "verify-result ok";
  } else {
    el.verifyResult.textContent = problems.join(" ");
    el.verifyResult.className = "verify-result warn";
  }
}

function exitPointFor(vertex, neighbor) {
  const start = state.vertexPositions.get(vertex);
  const end = state.vertexPositions.get(neighbor);
  if (!start || !end) return null;
  const key = edgeKey(vertex, neighbor);
  const controls = state.edgeRoutes.get(key) || [];
  const path = vertex < neighbor ? [start, ...controls, end] : [end, ...controls, start];
  const oriented = vertex < neighbor ? path : [...path].reverse();
  for (let i = 1; i < oriented.length; i++) {
    if (oriented[i].distanceToSquared(start) > 1e-10) return oriented[i];
  }
  return null;
}

function cyclicOrderEqual(actual, expected) {
  if (actual.length !== expected.length) return false;
  return expected.some((_, shift) => actual.every((value, index) => value === expected[(index + shift) % expected.length]));
}

function tangentFrame(normal) {
  const reference = Math.abs(normal.z) < 0.85 ? new THREE.Vector3(0, 0, 1) : new THREE.Vector3(1, 0, 0);
  const tangent = reference.cross(normal).normalize();
  const bitangent = normal.clone().cross(tangent).normalize();
  return { tangent, bitangent };
}

function normalAtPoint(point) {
  return projectToSurface(point).normal;
}

function saveLayout() {
  const payload = exportLayout();
  localStorage.setItem(storageKey(), JSON.stringify(payload));
  el.layoutJson.value = JSON.stringify(payload, null, 2);
  setStatus("Saved this layout locally.");
}

async function copyLayout() {
  const payload = JSON.stringify(exportLayout(), null, 2);
  el.layoutJson.value = payload;
  try {
    await navigator.clipboard.writeText(payload);
    setStatus("Copied layout JSON.");
  } catch {
    setStatus("Layout JSON is ready in the text box.");
  }
}

function applyLayout() {
  try {
    importLayout(JSON.parse(el.layoutJson.value));
    localStorage.setItem(storageKey(), JSON.stringify(exportLayout()));
    drawManualOverlay();
    setStatus("Applied layout JSON.");
  } catch (error) {
    setStatus(`Could not apply JSON: ${error.message}`);
  }
}

function loadSavedLayout() {
  const saved = localStorage.getItem(storageKey());
  if (!saved) return;
  try {
    importLayout(JSON.parse(saved));
    el.layoutJson.value = JSON.stringify(exportLayout(), null, 2);
  } catch {
    localStorage.removeItem(storageKey());
  }
}

function exportLayout() {
  return {
    representative: Number(el.representative.value || 0),
    mask: REPRESENTATIVES[Number(el.representative.value || 0)].mask,
    vertices: Object.fromEntries([...state.vertexPositions.entries()].map(([vertex, point]) => [vertex, vectorToArray(point)])),
    edges: Object.fromEntries([...state.edgeRoutes.entries()].map(([edge, points]) => [edge, points.map(vectorToArray)])),
  };
}

function importLayout(layout) {
  state.vertexPositions = new Map();
  state.edgeRoutes = new Map();
  Object.entries(layout.vertices || {}).forEach(([vertex, value]) => {
    state.vertexPositions.set(Number(vertex), arrayToVector(value));
  });
  Object.entries(layout.edges || {}).forEach(([edge, points]) => {
    state.edgeRoutes.set(edge, points.map(arrayToVector));
  });
}

function storageKey() {
  return `k33-genus2-manual-${el.representative.value || 0}`;
}

function currentRotation() {
  return rotationFromMask(REPRESENTATIVES[Number(el.representative.value || 0)].mask);
}

function rotationFromMask(mask) {
  return K33_BASE.map((neighbors, vertex) => {
    const ordered = [neighbors[0], neighbors[1], neighbors[2]];
    return ((mask >> vertex) & 1) ? [ordered[0], ordered[2], ordered[1]] : ordered;
  });
}

function parseObj(objText) {
  const vertices = [new THREE.Vector3()];
  const positions = [];
  const texcoords = [];
  const indices = [];
  const graphLines = [];
  const cornerIndices = new Map();
  const uvs = [[0, 0]];

  const addCorner = (token) => {
    const [vertexToken, textureToken] = token.split("/");
    const vertexIndex = Number(vertexToken);
    const textureIndex = textureToken ? Number(textureToken) : 0;
    const key = `${vertexIndex}/${textureIndex}`;
    if (cornerIndices.has(key)) return cornerIndices.get(key);
    const vertex = vertices[vertexIndex];
    const uv = uvs[textureIndex] || [0, 0];
    const index = positions.length / 3;
    positions.push(vertex.x, vertex.y, vertex.z);
    texcoords.push(uv[0], uv[1]);
    cornerIndices.set(key, index);
    return index;
  };

  for (const rawLine of objText.split(/\r?\n/)) {
    const line = rawLine.trim();
    if (line === "" || line.startsWith("#")) continue;
    const parts = line.split(/\s+/);
    if (parts[0] === "v") {
      vertices.push(new THREE.Vector3(Number(parts[1]), Number(parts[2]), Number(parts[3])));
    } else if (parts[0] === "vt") {
      uvs.push([Number(parts[1]), Number(parts[2])]);
    } else if (parts[0] === "f") {
      const face = parts.slice(1).map(addCorner);
      for (let i = 1; i < face.length - 1; i++) indices.push(face[0], face[i], face[i + 1]);
    } else if (parts[0] === "l") {
      const points = parts.slice(1).map((token) => vertices[Number(token.split("/")[0])]).filter(Boolean);
      if (points.length >= 2) graphLines.push({ points });
    }
  }

  const geometry = new THREE.BufferGeometry();
  geometry.setAttribute("position", new THREE.Float32BufferAttribute(positions, 3));
  geometry.setAttribute("uv", new THREE.Float32BufferAttribute(texcoords, 2));
  geometry.setIndex(indices);
  geometry.computeVertexNormals();
  geometry.normalizeNormals();
  return { geometry, graphLines };
}

function buildSurfaceTriangles(geometry) {
  const positions = geometry.getAttribute("position");
  const index = geometry.index;
  const triangles = [];
  const a = new THREE.Vector3();
  const b = new THREE.Vector3();
  const c = new THREE.Vector3();
  const normal = new THREE.Vector3();
  const ab = new THREE.Vector3();
  const ac = new THREE.Vector3();
  const faceCount = index ? index.count / 3 : positions.count / 3;

  for (let face = 0; face < faceCount; face++) {
    const i0 = index ? index.getX(face * 3) : face * 3;
    const i1 = index ? index.getX(face * 3 + 1) : face * 3 + 1;
    const i2 = index ? index.getX(face * 3 + 2) : face * 3 + 2;
    a.fromBufferAttribute(positions, i0);
    b.fromBufferAttribute(positions, i1);
    c.fromBufferAttribute(positions, i2);
    ab.subVectors(b, a);
    ac.subVectors(c, a);
    normal.crossVectors(ab, ac);
    if (normal.lengthSq() < 1e-14) continue;
    triangles.push({
      a: a.clone(),
      b: b.clone(),
      c: c.clone(),
      normal: normal.normalize().clone(),
    });
  }
  return triangles;
}

function projectToSurface(point) {
  const closest = new THREE.Vector3();
  const candidate = new THREE.Vector3();
  let bestDistanceSq = Infinity;
  let bestNormal = new THREE.Vector3(0, 0, 1);
  for (const triangle of state.surfaceTriangles) {
    closestPointOnTriangle(point, triangle.a, triangle.b, triangle.c, candidate);
    const distanceSq = point.distanceToSquared(candidate);
    if (distanceSq < bestDistanceSq) {
      bestDistanceSq = distanceSq;
      closest.copy(candidate);
      bestNormal = triangle.normal;
    }
  }
  if (!Number.isFinite(bestDistanceSq)) return { point: point.clone(), normal: bestNormal.clone(), distanceSq: Infinity };
  return { point: closest, normal: bestNormal.clone(), distanceSq: bestDistanceSq };
}

function closestPointOnTriangle(point, a, b, c, target) {
  const { ab, ac, ap, bp, cp, bc } = triangleScratch;
  ab.subVectors(b, a);
  ac.subVectors(c, a);
  ap.subVectors(point, a);
  const d1 = ab.dot(ap);
  const d2 = ac.dot(ap);
  if (d1 <= 0 && d2 <= 0) return target.copy(a);

  bp.subVectors(point, b);
  const d3 = ab.dot(bp);
  const d4 = ac.dot(bp);
  if (d3 >= 0 && d4 <= d3) return target.copy(b);

  const vc = d1 * d4 - d3 * d2;
  if (vc <= 0 && d1 >= 0 && d3 <= 0) {
    const v = d1 / (d1 - d3);
    return target.copy(a).addScaledVector(ab, v);
  }

  cp.subVectors(point, c);
  const d5 = ab.dot(cp);
  const d6 = ac.dot(cp);
  if (d6 >= 0 && d5 <= d6) return target.copy(c);

  const vb = d5 * d2 - d1 * d6;
  if (vb <= 0 && d2 >= 0 && d6 <= 0) {
    const w = d2 / (d2 - d6);
    return target.copy(a).addScaledVector(ac, w);
  }

  const va = d3 * d6 - d5 * d4;
  if (va <= 0 && d4 - d3 >= 0 && d5 - d6 >= 0) {
    const w = (d4 - d3) / (d4 - d3 + d5 - d6);
    bc.subVectors(c, b);
    return target.copy(b).addScaledVector(bc, w);
  }

  const denom = 1 / (va + vb + vc);
  const v = vb * denom;
  const w = vc * denom;
  return target.copy(a).addScaledVector(ab, v).addScaledVector(ac, w);
}

function makeTube(points, radius, material, segments = 32) {
  const clean = points.filter(Boolean).map((point) => point.clone());
  if (clean.length < 2) return new THREE.Mesh(new THREE.SphereGeometry(radius, 8, 6), material);
  const path = new THREE.CurvePath();
  for (let i = 0; i < clean.length - 1; i++) {
    if (clean[i].distanceToSquared(clean[i + 1]) > 1e-10) path.add(new THREE.LineCurve3(clean[i], clean[i + 1]));
  }
  if (path.curves.length === 0) return new THREE.Mesh(new THREE.SphereGeometry(radius, 8, 6), material);
  return new THREE.Mesh(new THREE.TubeGeometry(path, Math.max(1, segments), radius, 6, false), material);
}

function polylineLength(points) {
  let total = 0;
  for (let i = 0; i < points.length - 1; i++) total += points[i].distanceTo(points[i + 1]);
  return total;
}

function makeTextSprite(text, size) {
  const canvas = document.createElement("canvas");
  const context = canvas.getContext("2d");
  const fontSize = 44;
  const padding = 14;
  context.font = `800 ${fontSize}px system-ui, sans-serif`;
  const metrics = context.measureText(text);
  canvas.width = Math.ceil(metrics.width + padding * 2);
  canvas.height = fontSize + padding * 2;
  context.font = `800 ${fontSize}px system-ui, sans-serif`;
  context.textBaseline = "middle";
  context.lineWidth = 8;
  context.strokeStyle = "rgba(247, 247, 244, 0.96)";
  context.fillStyle = "#111";
  context.strokeText(text, padding, canvas.height / 2);
  context.fillText(text, padding, canvas.height / 2);
  const texture = new THREE.CanvasTexture(canvas);
  texture.colorSpace = THREE.SRGBColorSpace;
  const material = new THREE.SpriteMaterial({ map: texture, transparent: true, depthTest: true, depthWrite: false });
  const sprite = new THREE.Sprite(material);
  sprite.scale.set(size * (canvas.width / canvas.height), size, 1);
  sprite.userData.dispose = () => {
    texture.dispose();
    material.dispose();
  };
  return sprite;
}

function clearGroup(group) {
  group.userData.dispose?.();
  delete group.userData.dispose;
  while (group.children.length) disposeObject(group.children.pop());
}

function disposeObject(object) {
  object.traverse?.((child) => {
    if (child.geometry) child.geometry.dispose();
    if (child.material) {
      const materials = Array.isArray(child.material) ? child.material : [child.material];
      materials.forEach((material) => {
        if (material.map) material.map.dispose();
        material.dispose();
      });
    }
    if (child.userData?.dispose && child !== object) child.userData.dispose();
  });
}

function resize() {
  const width = el.viewer.clientWidth || window.innerWidth;
  const height = el.viewer.clientHeight || window.innerHeight;
  renderer.setSize(width, height, false);
  camera.aspect = width / height;
  camera.updateProjectionMatrix();
}

function animate() {
  controls.update();
  renderer.render(scene, camera);
  requestAnimationFrame(animate);
}

function vectorToArray(vector) {
  return [round(vector.x), round(vector.y), round(vector.z)];
}

function arrayToVector(value) {
  if (!Array.isArray(value) || value.length < 3) throw new Error("Expected [x, y, z]");
  return new THREE.Vector3(Number(value[0]), Number(value[1]), Number(value[2]));
}

function round(value) {
  return Math.round(value * 1000000) / 1000000;
}

function edgeKey(a, b) {
  return a < b ? `${a}-${b}` : `${b}-${a}`;
}

function setStatus(message) {
  el.status.textContent = message;
}
