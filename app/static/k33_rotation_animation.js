// SPDX-FileCopyrightText: 2026 Alexander Metzger
// SPDX-License-Identifier: GPL-2.0-only

import * as THREE from "three";
import { OrbitControls } from "/vendor/OrbitControls.js";

const BLUE = 0x0867d8;
const BLACK = 0x151719;
const SURFACE = 0xc7cbc6;
const FACE_COLORS = [
  0x0a67c5, 0xb46a00, 0x237052, 0x7d4ac7, 0xbb3f4a, 0x47606f,
];
const TRACED_FACES_CAMERA_POSITION = new THREE.Vector3(0, -5.85, 3.15);
const TRACED_FACES_CAMERA_TARGET = new THREE.Vector3(0, 0, 0.2);
const SURFACE_CAMERA_POSITION = new THREE.Vector3(0, -6.15, 2.95);
const SURFACE_CAMERA_TARGET = new THREE.Vector3(0, 0, 0);
const TORUS_GLUE_DURATION = 1280;
const TORUS_GLUE_HOLD = 620;
const GENUS2_REPRESENTATIVE_MASK = 1;
const GENUS2_MANUAL_LAYOUT_URL = "k33_genus2_manual_layout.json";
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
const INTRO_EXPLANATION =
  "A rotation system defines a cyclic ordering of the incident edges (darts) for each vertex. Click each line to view.";
const START_TRACE_EXPLANATION = "We start by choosing an arbitrary dart.";
const FINISHED_FACE_EXPLANATION =
  "We have finished a face, so we choose an arbitrary unused dart.";
const ALL_DARTS_EXPLANATION =
  "We have used all the darts. Now we have the faces of a 3D surface which is formed by gluing the faces at matching edges.";
const FINAL_EXPLANATION =
  "In the final embedding, the cyclic ordering of the rotation system is oriented following the right-hand rule (counter-clockwise). Click each line to see.";

const el = {
  viewer: document.getElementById("viewer"),
  showEmbedding: document.getElementById("show_embedding"),
  status: document.getElementById("status"),
  playbackStart: document.getElementById("playback_start"),
  playbackBack: document.getElementById("playback_back"),
  playbackForward: document.getElementById("playback_forward"),
  playbackEnd: document.getElementById("playback_end"),
  rotationTitle: document.getElementById("rotation_title"),
  genusBadge: document.getElementById("genus_badge"),
  rotationList: document.getElementById("rotation_list"),
  explanationText: document.getElementById("explanation_text"),
  slider: document.getElementById("rotation_slider"),
  rotationNumber: document.getElementById("rotation_number"),
  sliderLabel: document.getElementById("slider_label"),
  nextRotation: document.getElementById("next_rotation"),
};

const systems = makeRotationSystems();
const modelCache = new Map();
const k33Automorphisms = makeK33Automorphisms();
let genusTwoManualLayoutPromise = null;
let genusTwoRawModelPromise = null;
let genusTwoBaseRenderDataPromise = null;
const mobileQuery = window.matchMedia("(max-width: 760px)");
const state = {
  index: 0,
  phase: "flat",
  sequenceToken: 0,
  animationToken: 0,
  manualMode: false,
  manualStep: -1,
  cameraToken: 0,
  modelGroup: null,
  flatGroup: null,
  faceGroup: new THREE.Group(),
  traceGroup: new THREE.Group(),
  highlightGroup: new THREE.Group(),
  vertexHighlightGroup: new THREE.Group(),
  arrowGroup: new THREE.Group(),
  surfacePaths: new Map(),
  surfaceVertices: new Map(),
  surfaceCenter: new THREE.Vector3(),
  surfaceNormalAt: null,
  surfaceStrokeRadius: 0.006,
  finalOpacity: null,
};

const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
renderer.outputColorSpace = THREE.SRGBColorSpace;
el.viewer.appendChild(renderer.domElement);

const scene = new THREE.Scene();
scene.background = new THREE.Color(0xf7f7f3);
const camera = new THREE.PerspectiveCamera(42, 1, 0.01, 100);
camera.position.set(0, 0, 6.8);
const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true;
controls.enableRotate = false;
controls.enablePan = false;
controls.target.set(0, 0, 0);

scene.add(new THREE.HemisphereLight(0xffffff, 0x8b8d88, 2.15));
const key = new THREE.DirectionalLight(0xffffff, 1.8);
key.position.set(4, -5, 7);
scene.add(key);
scene.add(state.faceGroup);
scene.add(state.traceGroup);
scene.add(state.highlightGroup);
scene.add(state.vertexHighlightGroup);
scene.add(state.arrowGroup);

const resizeObserver = new ResizeObserver(resize);
resizeObserver.observe(el.viewer);
resize();
setRotation(0);
animate();
prefetchGenusTwo();
setTimeout(prefetchNearby, 750);

el.slider.addEventListener("input", () => setRotation(Number(el.slider.value)));
el.rotationNumber.addEventListener("input", () => {
  const value = Number(el.rotationNumber.value);
  if (Number.isInteger(value) && value >= 1 && value <= systems.length) {
    setRotation(value - 1);
  }
});
el.rotationNumber.addEventListener("change", () => {
  const value = clampRotationNumber(el.rotationNumber.value);
  el.rotationNumber.value = String(value);
  if (value !== state.index + 1) setRotation(value - 1);
});
el.showEmbedding.addEventListener("click", showEmbedding);
el.playbackStart.addEventListener("click", () => usePlayback("start"));
el.playbackBack.addEventListener("click", () => usePlayback("back"));
el.playbackForward.addEventListener("click", () => usePlayback("forward"));
el.playbackEnd.addEventListener("click", () => usePlayback("end"));
el.nextRotation.addEventListener("click", () =>
  setRotation((state.index + 1) % systems.length),
);
mobileQuery.addEventListener("change", () =>
  setShowEmbeddingLabel(currentSystem()),
);

function makeRotationSystems() {
  const all = [];
  for (let mask = 0; mask < 64; mask++) {
    const rotation = rotationFromMask(mask);
    const faces = computeFaces(rotation);
    all.push({
      index: mask,
      rotation,
      faces,
      genus: genusFromFaces(rotation, faces),
    });
  }
  return all;
}

function rotationFromMask(mask) {
  return K33_BASE.map((neighbors, vertex) => {
    const ordered = [neighbors[0], neighbors[1], neighbors[2]];
    if ((mask >> vertex) & 1) return [ordered[0], ordered[2], ordered[1]];
    return ordered;
  });
}

function computeFaces(rotation) {
  const darts = [];
  const next = new Map();
  rotation.forEach((neighbors, vertex) => {
    neighbors.forEach((neighbor) => darts.push(dartKey(vertex, neighbor)));
    neighbors.forEach((incoming, index) => {
      const outgoing = neighbors[(index + 1) % neighbors.length];
      next.set(dartKey(incoming, vertex), [vertex, outgoing]);
    });
  });

  const visited = new Set();
  const faces = [];
  for (const startKey of darts) {
    if (visited.has(startKey)) continue;
    const face = [];
    let [from, to] = startKey.split("-").map(Number);
    while (!visited.has(dartKey(from, to))) {
      visited.add(dartKey(from, to));
      face.push({ from, to });
      [from, to] = next.get(dartKey(from, to));
    }
    faces.push(face);
  }
  return faces;
}

function genusFromFaces(rotation, faces) {
  const vertices = rotation.length;
  const edges =
    rotation.reduce((sum, neighbors) => sum + neighbors.length, 0) / 2;
  return (2 - (vertices - edges + faces.length)) / 2;
}

function setRotation(index) {
  state.animationToken++;
  state.sequenceToken++;
  state.index = index;
  state.manualMode = false;
  state.manualStep = -1;

  const system = currentSystem();
  el.slider.value = String(index);
  el.rotationTitle.textContent = `Rotation ${index + 1} / 64`;
  el.genusBadge.textContent = `genus ${system.genus}`;
  el.sliderLabel.textContent = `Rotation ${index + 1} of 64`;
  el.rotationNumber.value = String(index + 1);
  setShowEmbeddingLabel(system);
  el.showEmbedding.disabled = false;
  el.status.textContent = "";
  setExplanation(INTRO_EXPLANATION);
  buildRotationList(system);
  resetToFlatScene();
}

function currentSystem() {
  return systems[state.index];
}

function setExplanation(text) {
  el.explanationText.textContent = text;
}

function setShowEmbeddingLabel(system) {
  el.showEmbedding.textContent = mobileQuery.matches
    ? "Embed"
    : `Show Genus ${system.genus} Embedding`;
}

function rotationOrderText(order) {
  return `(${order.join(", ")})`;
}

function vertexRotationExplanation(system, vertex) {
  return `The local rotation at vertex ${vertex} has cyclic ordering ${rotationOrderText(system.rotation[vertex])}.`;
}

function nextAfterIncoming(system, vertex, incoming) {
  const rotation = system.rotation[vertex];
  const index = rotation.indexOf(incoming);
  if (index === -1) return rotation[0];
  return rotation[(index + 1) % rotation.length];
}

function traceStepExplanation(system, step) {
  if (step <= 0) return START_TRACE_EXPLANATION;
  step -= 1;
  const timeline = traceTimeline(system);
  const current = timeline[step];
  if (!current) return ALL_DARTS_EXPLANATION;
  const face = system.faces[current.faceIndex];
  const isLastDartInFace = current.dartIndex === face.length - 1;
  const isLastDartOverall = step === timeline.length - 1;
  if (isLastDartInFace && !isLastDartOverall) return FINISHED_FACE_EXPLANATION;
  const x = current.dart.to;
  const y = current.dart.from;
  const z = nextAfterIncoming(system, x, y);
  return `We entered ${x} from ${y} so the next vertex after ${y} in ${x}'s local rotation is ${z}.`;
}

function buildRotationList(system) {
  el.rotationList.replaceChildren();
  system.rotation.forEach((neighbors, vertex) => {
    const row = document.createElement("button");
    row.type = "button";
    row.className = "rotation-row";
    row.dataset.vertex = String(vertex);
    row.innerHTML = `
      <span class="vertex-id">${vertex}</span>
      <span class="neighbor-list">
        <span class="cycle-mark">(</span>
        ${neighbors.map((neighbor) => `<span class="neighbor-chip" data-dart="${vertex}-${neighbor}">${neighbor}</span>`).join("")}
        <span class="cycle-mark">)</span>
      </span>
    `;
    row.addEventListener("click", () => playVertexRotation(vertex));
    el.rotationList.appendChild(row);
  });
}

function flatPosition(vertex) {
  const y = [1.35, 0, -1.35][vertex % 3];
  const x = vertex < 3 ? -1.72 : 1.72;
  return new THREE.Vector3(x, y, 0);
}

function buildFlatGraph() {
  if (state.flatGroup) {
    disposeGroup(state.flatGroup);
    scene.remove(state.flatGroup);
  }
  const group = new THREE.Group();
  const edgeMaterial = makeBasicMaterial(BLACK, 0.88);
  const pointMaterial = makeBasicMaterial(0xf4f4ef, 1);
  const pointRingMaterial = makeBasicMaterial(BLACK, 1);

  for (const [a, b] of EDGES) {
    const points = [flatPosition(a), flatPosition(b)];
    const tube = makeTube(points, 0.014, edgeMaterial, 24);
    tube.userData.edge = edgeKey(a, b);
    group.add(tube);
  }

  for (let vertex = 0; vertex < 6; vertex++) {
    const p = flatPosition(vertex);
    const dot = new THREE.Mesh(
      new THREE.SphereGeometry(0.075, 24, 16),
      pointMaterial,
    );
    dot.position.copy(p);
    group.add(dot);
    const ring = new THREE.Mesh(
      new THREE.SphereGeometry(0.082, 24, 12),
      pointRingMaterial,
    );
    ring.position.copy(p);
    ring.scale.setScalar(1.02);
    ring.material.side = THREE.BackSide;
    group.add(ring);
    const label = makeTextSprite(String(vertex), 0.22, { depthTest: false });
    label.position
      .copy(p)
      .add(new THREE.Vector3(vertex < 3 ? -0.2 : 0.2, 0.12, 0.04));
    group.add(label);
  }

  group.userData.dispose = () => {
    edgeMaterial.dispose();
    pointMaterial.dispose();
    pointRingMaterial.dispose();
    disposeGroupChildren(group);
  };
  state.flatGroup = group;
  scene.add(group);
}

function setCameraFlat() {
  controls.enableRotate = false;
  controls.enablePan = false;
  animateCamera(new THREE.Vector3(0, 0, 6.8), new THREE.Vector3(0, 0, 0), 360);
}

function resetToFlatScene() {
  state.phase = "flat";
  clearGroup(state.highlightGroup);
  clearGroup(state.traceGroup);
  clearGroup(state.vertexHighlightGroup);
  clearGroup(state.arrowGroup);
  clearGroup(state.faceGroup);
  disposeModelGroup();
  clearActiveList();
  buildFlatGraph();
  setGroupOpacity(state.flatGroup, 1);
  setCameraFlat();
}

async function playVertexRotation(vertex) {
  const token = ++state.sequenceToken;
  clearActiveList();
  clearGroup(state.vertexHighlightGroup);
  highlightVertex(vertex);
  const system = currentSystem();
  setExplanation(vertexRotationExplanation(system, vertex));
  const darts = system.rotation[vertex].map((to) => ({ from: vertex, to }));
  if (state.phase === "surface") animateCounterclockwiseArrow(vertex, token);

  for (const dart of darts) {
    if (token !== state.sequenceToken) return;
    highlightDart(dart);
    await delay(520);
  }
}

async function showEmbedding() {
  const system = currentSystem();
  const token = ++state.animationToken;
  state.sequenceToken++;
  state.manualMode = false;
  state.manualStep = -1;
  resetToFlatScene();
  setExplanation(INTRO_EXPLANATION);
  el.showEmbedding.disabled = true;
  el.slider.disabled = true;
  el.rotationNumber.disabled = true;
  el.status.textContent = "Resetting view";
  await delay(360);
  if (token !== state.animationToken) return;
  state.phase = "tracing";
  el.status.textContent = "Tracing faces";
  clearGroup(state.highlightGroup);
  clearGroup(state.traceGroup);
  clearGroup(state.vertexHighlightGroup);
  clearGroup(state.arrowGroup);
  clearGroup(state.faceGroup);
  if (state.modelGroup) disposeModelGroup();

  let modelPromise = getModel(system);
  await traceFaces(system, token);
  if (token !== state.animationToken) return;

  setExplanation(ALL_DARTS_EXPLANATION);
  el.status.textContent = "Showing traced faces";
  await Promise.all([
    animateCamera(
      TRACED_FACES_CAMERA_POSITION,
      TRACED_FACES_CAMERA_TARGET,
      980,
    ),
    morphTraceDartsToFaceCycles(system, token),
  ]);
  if (token !== state.animationToken) return;

  el.status.textContent = "Showing traced faces";
  await delay(1120);
  if (token !== state.animationToken) return;

  el.status.textContent = "Gluing to the torus";
  const model = await modelPromise;
  if (token !== state.animationToken) return;
  const modelGroup = buildModelGroup(model);
  state.modelGroup = modelGroup.group;
  state.surfacePaths = modelGroup.pathsByEdge;
  state.surfaceVertices = modelGroup.vertexPositions;
  state.surfaceNormalAt = modelGroup.normalAt || torusNormal;
  state.finalOpacity = modelGroup.setOpacity;
  modelGroup.setOpacity(0);
  scene.add(modelGroup.group);

  controls.enableRotate = true;
  controls.enablePan = true;
  await Promise.all([
    animateCamera(
      SURFACE_CAMERA_POSITION,
      SURFACE_CAMERA_TARGET,
      TORUS_GLUE_DURATION,
    ),
    morphFaceCyclesToSurface(system, modelGroup, token),
  ]);
  if (token !== state.animationToken) return;
  await delay(TORUS_GLUE_HOLD);
  if (token !== state.animationToken) return;
  await crossFadeToSurface(modelGroup.setOpacity, token);
  if (token !== state.animationToken) return;

  state.phase = "surface";
  state.manualMode = false;
  state.manualStep = traceTimeline(system).length + 1;
  setExplanation(FINAL_EXPLANATION);
  clearGroup(state.highlightGroup);
  clearGroup(state.traceGroup);
  clearGroup(state.vertexHighlightGroup);
  clearActiveList();
  el.status.textContent = "";
  el.showEmbedding.disabled = false;
  el.slider.disabled = false;
  el.rotationNumber.disabled = false;
}

async function usePlayback(action) {
  const system = currentSystem();
  state.manualMode = true;
  const token = ++state.animationToken;
  state.sequenceToken++;

  const timeline = traceTimeline(system);
  const finalStep = timeline.length + 1;
  const current = state.phase === "surface" ? finalStep : state.manualStep;
  let next = current;

  if (action === "start") next = -1;
  else if (action === "back") next = Math.max(-1, current - 1);
  else if (action === "forward") next = Math.min(finalStep, current + 1);
  else if (action === "end") next = finalStep;

  await renderManualStep(system, next, token, {
    animateBoundary: action === "forward",
  });
}

async function renderManualStep(system, step, token, options = {}) {
  const timeline = traceTimeline(system);
  const facesStep = timeline.length;
  const finalStep = timeline.length + 1;
  const previousStep = state.phase === "surface" ? finalStep : state.manualStep;
  state.manualStep = Math.max(-1, Math.min(finalStep, step));
  const animateBoundary = options.animateBoundary === true;
  el.showEmbedding.disabled = false;
  el.slider.disabled = state.manualStep > -1;
  el.rotationNumber.disabled = state.manualStep > -1;

  if (state.manualStep === -1) {
    state.manualMode = false;
    resetToFlatScene();
    setExplanation(INTRO_EXPLANATION);
    el.status.textContent = "";
    return;
  }

  if (state.manualStep < facesStep) {
    resetManualTraceScene();
    renderTracePrefix(system, state.manualStep);
    const current = timeline[state.manualStep];
    setExplanation(traceStepExplanation(system, state.manualStep));
    el.status.textContent = `Tracing face ${current.faceIndex + 1} / ${system.faces.length}`;
    return;
  }

  if (state.manualStep === facesStep) {
    resetManualTraceScene();
    if (animateBoundary && previousStep === facesStep - 1) {
      renderTracePrefix(system, timeline.length - 1, {
        highlightCurrent: false,
      });
      setExplanation(ALL_DARTS_EXPLANATION);
      el.status.textContent = "Showing traced faces";
      await Promise.all([
        animateCamera(
          TRACED_FACES_CAMERA_POSITION,
          TRACED_FACES_CAMERA_TARGET,
          980,
        ),
        morphTraceDartsToFaceCycles(system, token),
      ]);
      return;
    }
    renderLiftedFaces(system);
    setGroupOpacity(state.flatGroup, 0.18);
    setCameraPose(TRACED_FACES_CAMERA_POSITION, TRACED_FACES_CAMERA_TARGET);
    setExplanation(ALL_DARTS_EXPLANATION);
    el.status.textContent = "Showing traced faces";
    return;
  }

  if (animateBoundary && previousStep === facesStep) {
    el.status.textContent = "Gluing to the torus";
    resetManualTraceScene();
    renderLiftedFaces(system);
    setGroupOpacity(state.flatGroup, 0.18);
    setCameraPose(TRACED_FACES_CAMERA_POSITION, TRACED_FACES_CAMERA_TARGET);
    const model = await getModel(system);
    if (token !== state.animationToken || !state.manualMode) return;
    disposeModelGroup();
    const modelGroup = buildModelGroup(model);
    state.modelGroup = modelGroup.group;
    state.surfacePaths = modelGroup.pathsByEdge;
    state.surfaceVertices = modelGroup.vertexPositions;
    state.surfaceNormalAt = modelGroup.normalAt || torusNormal;
    state.finalOpacity = modelGroup.setOpacity;
    modelGroup.setOpacity(0);
    scene.add(modelGroup.group);
    state.phase = "surface";
    controls.enableRotate = true;
    controls.enablePan = true;
    await Promise.all([
      animateCamera(
        SURFACE_CAMERA_POSITION,
        SURFACE_CAMERA_TARGET,
        TORUS_GLUE_DURATION,
      ),
      morphFaceCyclesToSurface(system, modelGroup, token),
    ]);
    if (token !== state.animationToken || !state.manualMode) return;
    await delay(TORUS_GLUE_HOLD);
    if (token !== state.animationToken || !state.manualMode) return;
    await crossFadeToSurface(modelGroup.setOpacity, token);
    if (token !== state.animationToken || !state.manualMode) return;
    state.manualMode = false;
    state.manualStep = finalStep;
    setExplanation(FINAL_EXPLANATION);
    clearActiveList();
    clearGroup(state.highlightGroup);
    clearGroup(state.traceGroup);
    clearGroup(state.vertexHighlightGroup);
    el.status.textContent = "";
    el.showEmbedding.disabled = false;
    el.slider.disabled = false;
    el.rotationNumber.disabled = false;
    return;
  }

  el.status.textContent = "Loading final surface";
  resetManualTraceScene();
  setGroupOpacity(state.flatGroup, 0);
  clearGroup(state.traceGroup);
  clearGroup(state.faceGroup);
  const model = await getModel(system);
  if (token !== state.animationToken || !state.manualMode) return;
  disposeModelGroup();
  const modelGroup = buildModelGroup(model);
  state.modelGroup = modelGroup.group;
  state.surfacePaths = modelGroup.pathsByEdge;
  state.surfaceVertices = modelGroup.vertexPositions;
  state.surfaceNormalAt = modelGroup.normalAt || torusNormal;
  state.finalOpacity = modelGroup.setOpacity;
  modelGroup.setOpacity(1, true);
  scene.add(modelGroup.group);
  state.phase = "surface";
  controls.enableRotate = true;
  controls.enablePan = true;
  setCameraPose(SURFACE_CAMERA_POSITION, SURFACE_CAMERA_TARGET);
  clearActiveList();
  clearGroup(state.highlightGroup);
  clearGroup(state.vertexHighlightGroup);
  el.status.textContent = "";
  state.manualMode = false;
  state.manualStep = finalStep;
  setExplanation(FINAL_EXPLANATION);
  el.showEmbedding.disabled = false;
  el.slider.disabled = false;
  el.rotationNumber.disabled = false;
}

function resetManualTraceScene() {
  state.phase = "tracing";
  clearGroup(state.highlightGroup);
  clearGroup(state.traceGroup);
  clearGroup(state.vertexHighlightGroup);
  clearGroup(state.arrowGroup);
  clearGroup(state.faceGroup);
  disposeModelGroup();
  clearActiveList();
  buildFlatGraph();
  setGroupOpacity(state.flatGroup, 1);
  controls.enableRotate = false;
  controls.enablePan = false;
  setCameraPose(new THREE.Vector3(0, 0, 6.8), new THREE.Vector3(0, 0, 0));
}

function clearTraceSelection() {
  clearGroup(state.highlightGroup);
  clearGroup(state.vertexHighlightGroup);
  clearActiveList();
}

function renderTracePrefix(system, step, options = {}) {
  const highlightCurrent = options.highlightCurrent ?? true;
  const timeline = traceTimeline(system);
  for (let i = 0; i <= step && i < timeline.length; i++) {
    const item = timeline[i];
    addTraceDart(item.dart, FACE_COLORS[item.faceIndex % FACE_COLORS.length]);
  }
  const current = timeline[step];
  if (highlightCurrent && current) {
    highlightDart(
      current.dart,
      FACE_COLORS[current.faceIndex % FACE_COLORS.length],
    );
  }
}

function renderLiftedFaces(system) {
  addAllFaceCycles(system);
  const faces = [...state.faceGroup.children];
  faces.forEach((face, index) => {
    face.userData.setOpacity?.(1);
    applyLiftedFacePose(face, index, system.faces.length, 1);
  });
  clearTraceSelection();
}

function addAllFaceCycles(system) {
  for (let faceIndex = 0; faceIndex < system.faces.length; faceIndex++) {
    addFaceCycle(system.faces[faceIndex], faceIndex, system.faces.length);
  }
}

function traceTimeline(system) {
  const timeline = [];
  system.faces.forEach((face, faceIndex) => {
    face.forEach((dart, dartIndex) => {
      timeline.push({ dart, faceIndex, dartIndex });
    });
  });
  return timeline;
}

async function traceFaces(system, token) {
  let step = -1;
  for (let faceIndex = 0; faceIndex < system.faces.length; faceIndex++) {
    const face = system.faces[faceIndex];
    if (token !== state.animationToken) return;
    if (faceIndex === 0) setExplanation(START_TRACE_EXPLANATION);
    el.status.textContent = `Tracing face ${faceIndex + 1} / ${system.faces.length}`;
    for (const dart of face) {
      step += 1;
      if (token !== state.animationToken) return;
      state.manualStep = step;
      if (step > 0) setExplanation(traceStepExplanation(system, step));
      addTraceDart(dart, FACE_COLORS[faceIndex % FACE_COLORS.length]);
      highlightDart(dart, FACE_COLORS[faceIndex % FACE_COLORS.length]);
      await delay(620);
    }
    addFaceCycle(face, faceIndex, system.faces.length);
    if (faceIndex < system.faces.length - 1) {
      setExplanation(FINISHED_FACE_EXPLANATION);
    } else {
      setExplanation(ALL_DARTS_EXPLANATION);
    }
    await delay(290);
  }
}

function addFaceCycle(face, faceIndex, totalFaces) {
  const group = new THREE.Group();
  group.userData.baseOpacity = 0;
  const color = FACE_COLORS[faceIndex % FACE_COLORS.length];
  const material = makeBasicMaterial(color, 0);
  const pointMaterial = makeBasicMaterial(0xffffff, 0);
  const layout = faceCycleLayout(face, faceIndex, totalFaces);
  const points = layout.points;
  const tube = makeTube(points, 0.013, material, face.length * 12);
  tube.renderOrder = 20;
  group.add(tube);

  for (let i = 0; i < face.length; i++) {
    const arrowFrom = new THREE.Vector3().lerpVectors(
      points[i],
      points[i + 1],
      0.8,
    );
    const arrowTo = new THREE.Vector3().lerpVectors(
      points[i],
      points[i + 1],
      0.96,
    );
    group.add(
      makeArrowHead(arrowFrom, arrowTo, color, 0.03, 0.074, {
        depthTest: true,
        renderOrder: 22,
        opacity: 0,
        tipAtTarget: true,
      }),
    );
  }

  for (let i = 0; i < face.length; i++) {
    const pos = points[i].clone();
    const dot = new THREE.Mesh(
      new THREE.SphereGeometry(0.035, 16, 10),
      pointMaterial,
    );
    dot.position.copy(pos);
    dot.renderOrder = 30;
    group.add(dot);
    const label = makeTextSprite(`${face[i].from}`, 0.13, {
      depthTest: false,
      opacity: 0,
    });
    label.position.copy(pos).add(new THREE.Vector3(0.06, -0.05, 0.05));
    group.add(label);
  }

  group.userData.setOpacity = (opacity) => {
    group.traverse((child) => {
      if (child.material) {
        const materials = Array.isArray(child.material)
          ? child.material
          : [child.material];
        materials.forEach((mat) => {
          mat.opacity = opacity;
          mat.transparent = true;
        });
      }
    });
  };
  group.userData.dispose = () => {
    material.dispose();
    pointMaterial.dispose();
    disposeGroupChildren(group);
  };
  state.faceGroup.add(group);
}

function faceCycleLayout(face, faceIndex, totalFaces) {
  const radius = Math.max(0.42, Math.min(0.82, 0.28 + face.length * 0.035));
  const slotWidth = Math.max(
    1.18,
    Math.min(2.15, 5.4 / Math.max(1, totalFaces)),
  );
  const slotX = (faceIndex - (totalFaces - 1) / 2) * slotWidth;
  const zLift = 1.42 + (faceIndex % 2) * 0.16;
  const center = new THREE.Vector3(slotX, -0.22, zLift);
  const points = [];
  for (let i = 0; i <= face.length; i++) {
    const angle = Math.PI / 2 - (i / face.length) * Math.PI * 2;
    points.push(
      new THREE.Vector3(
        center.x + Math.cos(angle) * radius,
        center.y,
        center.z + Math.sin(angle) * radius,
      ),
    );
  }
  return { points };
}

function applyLiftedFacePose(face, faceIndex, totalFaces, amount) {
  face.position.y = -0.26 * amount;
  face.rotation.x = -0.22 * amount;
  face.rotation.z = (faceIndex - (totalFaces - 1) / 2) * 0.04 * amount;
  face.scale.setScalar(1);
}

function liftedFaceMatrix(faceIndex, totalFaces) {
  const rotation = new THREE.Euler(
    -0.22,
    0,
    (faceIndex - (totalFaces - 1) / 2) * 0.04,
  );
  return new THREE.Matrix4().compose(
    new THREE.Vector3(0, -0.26, 0),
    new THREE.Quaternion().setFromEuler(rotation),
    new THREE.Vector3(1, 1, 1),
  );
}

function ensureFaceCycles(system) {
  if (state.faceGroup.children.length === system.faces.length) return;
  clearGroup(state.faceGroup);
  addAllFaceCycles(system);
}

function faceDartMorphs(system) {
  const morphs = [];
  system.faces.forEach((face, faceIndex) => {
    const layout = faceCycleLayout(face, faceIndex, system.faces.length);
    const matrix = liftedFaceMatrix(faceIndex, system.faces.length);
    face.forEach((dart, dartIndex) => {
      morphs.push({
        dart,
        color: FACE_COLORS[faceIndex % FACE_COLORS.length],
        fromStart: flatPosition(dart.from),
        toStart: flatPosition(dart.to),
        fromEnd: layout.points[dartIndex].clone().applyMatrix4(matrix),
        toEnd: layout.points[dartIndex + 1].clone().applyMatrix4(matrix),
      });
    });
  });
  return morphs;
}

async function morphTraceDartsToFaceCycles(system, token) {
  const duration = 980;
  const start = performance.now();
  clearTraceSelection();
  ensureFaceCycles(system);
  const faces = [...state.faceGroup.children];
  const morphs = faceDartMorphs(system);
  while (performance.now() - start < duration) {
    if (token !== state.animationToken) return;
    const t = easeInOut((performance.now() - start) / duration);
    const cycleOpacity = Math.max(0, (t - 0.74) / 0.26);
    setGroupOpacity(state.flatGroup, 1 - t * 0.82);
    faces.forEach((face, index) => {
      face.userData.setOpacity?.(cycleOpacity);
      applyLiftedFacePose(face, index, system.faces.length, t);
    });
    drawMorphDarts(morphs, t);
    await nextFrame();
  }
  setGroupOpacity(state.flatGroup, 0.18);
  faces.forEach((face, index) => {
    face.userData.setOpacity?.(1);
    applyLiftedFacePose(face, index, system.faces.length, 1);
  });
  clearGroup(state.traceGroup);
  clearTraceSelection();
}

function drawMorphDarts(morphs, amount) {
  clearGroup(state.traceGroup);
  for (const morph of morphs) {
    const from = new THREE.Vector3().lerpVectors(
      morph.fromStart,
      morph.fromEnd,
      amount,
    );
    const to = new THREE.Vector3().lerpVectors(
      morph.toStart,
      morph.toEnd,
      amount,
    );
    addDartVisualBetween(from, to, morph.color, state.traceGroup, 0.018, true);
  }
}

async function morphFaceCyclesToSurface(system, modelGroup, token) {
  const morph = surfaceGlueMorphData(
    system,
    modelGroup.pathsByEdge,
    modelGroup.vertexPositions,
  );
  const start = performance.now();
  while (performance.now() - start < TORUS_GLUE_DURATION) {
    if (token !== state.animationToken) return;
    const t = easeInOut((performance.now() - start) / TORUS_GLUE_DURATION);
    setGroupOpacity(state.flatGroup, 0.18 * (1 - t));
    state.faceGroup.children.forEach((face) => {
      face.userData.setOpacity?.(1 - t);
    });
    drawSurfaceGlueMorph(morph, t);
    await nextFrame();
  }
  setGroupOpacity(state.flatGroup, 0);
  state.faceGroup.children.forEach((face) => face.userData.setOpacity?.(0));
  drawSurfaceGlueMorph(morph, 1);
}

function surfaceGlueMorphData(system, pathsByEdge, vertexPositions) {
  const darts = [];
  const vertices = [];
  system.faces.forEach((face, faceIndex) => {
    const layout = faceCycleLayout(face, faceIndex, system.faces.length);
    const matrix = liftedFaceMatrix(faceIndex, system.faces.length);
    face.forEach((dart, dartIndex) => {
      const color = FACE_COLORS[faceIndex % FACE_COLORS.length];
      const startFrom = layout.points[dartIndex].clone().applyMatrix4(matrix);
      const startTo = layout.points[dartIndex + 1].clone().applyMatrix4(matrix);
      const targetPath = directedSurfacePath(
        dart,
        pathsByEdge,
        vertexPositions,
      );
      const samples = Math.max(24, Math.min(96, targetPath.length || 2));
      darts.push({
        color,
        startPath: resamplePolyline([startFrom, startTo], samples),
        targetPath: resamplePolyline(targetPath, samples),
      });
      vertices.push({
        start: startFrom,
        target: (vertexPositions.get(dart.from) || startFrom).clone(),
      });
    });
  });
  return {
    darts,
    vertices,
    edgeRadiusStart: 0.018,
    edgeRadiusEnd: Math.max(state.surfaceStrokeRadius * 1.75, 0.01),
    pointRadiusStart: 0.035,
    pointRadiusEnd: Math.max(state.surfaceStrokeRadius * 2.05, 0.018),
  };
}

function directedSurfacePath(dart, pathsByEdge, vertexPositions) {
  const start = vertexPositions.get(dart.from);
  const end = vertexPositions.get(dart.to);
  const segments = pathsByEdge.get(edgeKey(dart.from, dart.to)) || [];
  const pieces = segments
    .map((segment) => segment.points.map((point) => point.clone()))
    .filter((points) => points.length >= 2);
  if (pieces.length === 0) {
    if (start && end) return [start.clone(), end.clone()];
    return [new THREE.Vector3(), new THREE.Vector3()];
  }
  return stitchSurfacePieces(pieces, start, end);
}

function stitchSurfacePieces(pieces, start, end) {
  const remaining = pieces.map((points) =>
    points.map((point) => point.clone()),
  );
  const path = [];
  let current = start ? start.clone() : null;
  while (remaining.length) {
    let bestIndex = 0;
    let bestReverse = false;
    let bestDistance = Infinity;
    for (let i = 0; i < remaining.length; i++) {
      const piece = remaining[i];
      const first = piece[0];
      const last = piece[piece.length - 1];
      const firstDistance = current ? current.distanceToSquared(first) : 0;
      const lastDistance = current ? current.distanceToSquared(last) : 0;
      if (firstDistance < bestDistance) {
        bestDistance = firstDistance;
        bestIndex = i;
        bestReverse = false;
      }
      if (lastDistance < bestDistance) {
        bestDistance = lastDistance;
        bestIndex = i;
        bestReverse = true;
      }
    }
    const piece = remaining.splice(bestIndex, 1)[0];
    if (bestReverse) piece.reverse();
    if (path.length === 0) {
      if (current && current.distanceToSquared(piece[0]) > 1e-8)
        path.push(current.clone());
      path.push(...piece);
    } else {
      const last = path[path.length - 1];
      if (last.distanceToSquared(piece[0]) > 1e-8) path.push(piece[0].clone());
      path.push(...piece.slice(1));
    }
    current = path[path.length - 1].clone();
  }
  if (end && path[path.length - 1]?.distanceToSquared(end) > 1e-8)
    path.push(end.clone());
  return path;
}

function resamplePolyline(points, count) {
  const clean = points.filter(Boolean).map((point) => point.clone());
  if (clean.length === 0)
    return Array.from({ length: count }, () => new THREE.Vector3());
  if (clean.length === 1)
    return Array.from({ length: count }, () => clean[0].clone());
  const lengths = [0];
  for (let i = 1; i < clean.length; i++) {
    lengths.push(lengths[i - 1] + clean[i - 1].distanceTo(clean[i]));
  }
  const total = lengths[lengths.length - 1];
  if (total < 1e-8)
    return Array.from({ length: count }, () => clean[0].clone());
  const samples = [];
  let segment = 1;
  for (let i = 0; i < count; i++) {
    const d = total * (i / Math.max(1, count - 1));
    while (segment < lengths.length - 1 && lengths[segment] < d) segment++;
    const prev = clean[segment - 1];
    const next = clean[segment];
    const span = lengths[segment] - lengths[segment - 1];
    const t = span > 1e-8 ? (d - lengths[segment - 1]) / span : 0;
    samples.push(new THREE.Vector3().lerpVectors(prev, next, t));
  }
  return samples;
}

function drawSurfaceGlueMorph(morph, amount) {
  clearGroup(state.traceGroup);
  const edgeRadius = lerpScalar(
    morph.edgeRadiusStart,
    morph.edgeRadiusEnd,
    amount,
  );
  const pointRadius = lerpScalar(
    morph.pointRadiusStart,
    morph.pointRadiusEnd,
    amount,
  );
  for (const dart of morph.darts) {
    const points = dart.startPath.map((point, index) =>
      new THREE.Vector3().lerpVectors(point, dart.targetPath[index], amount),
    );
    addCurveDartVisual(points, dart.color, state.traceGroup, edgeRadius);
  }
  for (const vertex of morph.vertices) {
    const position = new THREE.Vector3().lerpVectors(
      vertex.start,
      vertex.target,
      amount,
    );
    addMorphVertexVisual(position, pointRadius, state.traceGroup);
  }
}

function addCurveDartVisual(points, color, group, radius) {
  if (points.length < 2) return;
  const material = makeBasicMaterial(color, 1, { depthTest: false });
  const tube = makeTube(
    points,
    radius,
    material,
    Math.max(8, points.length - 1),
  );
  tube.renderOrder = 24;
  group.add(tube);
  const headIndex = Math.max(0, points.length - 8);
  group.add(
    makeArrowHead(
      points[headIndex],
      points[points.length - 1],
      color,
      radius * 3.8,
      radius * 8.0,
    ),
  );
}

function addMorphVertexVisual(position, radius, group) {
  const dot = new THREE.Mesh(
    new THREE.SphereGeometry(radius, 18, 12),
    makeBasicMaterial(0xf4f4ef, 1, { depthTest: false }),
  );
  dot.position.copy(position);
  dot.renderOrder = 32;
  group.add(dot);
}

async function crossFadeToSurface(setOpacity, token) {
  const modelFadeDuration = 820;
  const colorFadeDuration = 620;
  const start = performance.now();
  while (performance.now() - start < modelFadeDuration) {
    if (token !== state.animationToken) return;
    const t = easeInOut((performance.now() - start) / modelFadeDuration);
    setOpacity(t);
    setGroupOpacity(state.flatGroup, 0);
    setGroupOpacity(state.traceGroup, 1);
    state.faceGroup.children.forEach((face) => {
      face.userData.setOpacity?.(0);
    });
    await nextFrame();
  }
  setOpacity(1, true);
  setGroupOpacity(state.flatGroup, 0);
  setGroupOpacity(state.traceGroup, 1);
  state.faceGroup.children.forEach((face) => face.userData.setOpacity?.(0));
  await nextFrame();
  await nextFrame();

  const fadeStart = performance.now();
  while (performance.now() - fadeStart < colorFadeDuration) {
    if (token !== state.animationToken) return;
    const t = easeInOut((performance.now() - fadeStart) / colorFadeDuration);
    setOpacity(1, true);
    setGroupOpacity(state.traceGroup, 1 - t);
    await nextFrame();
  }
  setOpacity(1, true);
  setGroupOpacity(state.traceGroup, 0);
  state.faceGroup.children.forEach((face) => face.userData.setOpacity?.(0));
}

async function getModel(system) {
  if (system.genus === 2) return getGenusTwoManualModel(system);
  const key = rotationKey(system.rotation);
  if (modelCache.has(key)) return modelCache.get(key);
  const model = await requestModel(system.rotation);
  modelCache.set(key, model);
  return model;
}

async function getGenusTwoManualModel(system) {
  const key = `manual-genus2:${system.index}`;
  if (modelCache.has(key)) return modelCache.get(key);
  const baseRenderData = await loadGenusTwoBaseRenderData();
  const automorphism = findAutomorphism(
    rotationFromMask(GENUS2_REPRESENTATIVE_MASK),
    system.rotation,
  );
  if (!automorphism)
    throw new Error(
      "Could not map the genus-2 representative to this rotation system.",
    );
  const model = {
    genus: 2,
    manualSurfaceData: baseRenderData,
    manualLayout: mapPreparedManualLayout(baseRenderData, automorphism),
  };
  modelCache.set(key, model);
  return model;
}

function prefetchGenusTwo() {
  loadGenusTwoBaseRenderData()
    .then((baseRenderData) => {
      for (const system of systems) {
        if (system.genus !== 2) continue;
        const automorphism = findAutomorphism(
          rotationFromMask(GENUS2_REPRESENTATIVE_MASK),
          system.rotation,
        );
        if (!automorphism) continue;
        const key = `manual-genus2:${system.index}`;
        if (!modelCache.has(key)) {
          modelCache.set(key, {
            genus: 2,
            manualSurfaceData: baseRenderData,
            manualLayout: mapPreparedManualLayout(baseRenderData, automorphism),
          });
        }
      }
    })
    .catch(() => {});
}

function loadGenusTwoManualLayout() {
  if (!genusTwoManualLayoutPromise) {
    genusTwoManualLayoutPromise = fetch(GENUS2_MANUAL_LAYOUT_URL).then(
      (response) => {
        if (!response.ok)
          throw new Error("Could not load the saved genus-2 manual layout.");
        return response.json();
      },
    );
  }
  return genusTwoManualLayoutPromise;
}

function requestGenusTwoRawModel() {
  if (!genusTwoRawModelPromise) {
    genusTwoRawModelPromise = requestModel(
      rotationFromMask(GENUS2_REPRESENTATIVE_MASK),
      "3d_raw",
    ).catch((error) => {
      genusTwoRawModelPromise = null;
      throw error;
    });
  }
  return genusTwoRawModelPromise;
}

function loadGenusTwoBaseRenderData() {
  if (!genusTwoBaseRenderDataPromise) {
    genusTwoBaseRenderDataPromise = Promise.all([
      loadGenusTwoManualLayout(),
      requestGenusTwoRawModel(),
    ])
      .then(([layout, rawModel]) =>
        prepareGenusTwoBaseRenderData(layout, rawModel),
      )
      .catch((error) => {
        genusTwoBaseRenderDataPromise = null;
        throw error;
      });
  }
  return genusTwoBaseRenderDataPromise;
}

function prepareGenusTwoBaseRenderData(layout, rawModel) {
  const parsed = parseObj(rawModel.obj);
  parsed.geometry.computeBoundingBox();
  const center = new THREE.Vector3();
  parsed.geometry.boundingBox.getCenter(center);
  parsed.geometry.translate(-center.x, -center.y, -center.z);
  parsed.geometry.computeBoundingSphere();
  const surfaceTriangles = buildSurfaceTriangles(parsed.geometry);
  const radius = parsed.geometry.boundingSphere?.radius || 1;
  const strokeRadius = Math.max(radius * 0.0032, 0.0048);
  const graphLift = strokeRadius * 0.18;
  const normalAt = (point) =>
    orientedProjectToSurface(point, surfaceTriangles).normal;
  const vertices = new Map();
  Object.entries(layout.vertices || {}).forEach(([vertex, point]) => {
    vertices.set(
      Number(vertex),
      liftPointToSurface(
        arrayToVector(point),
        surfaceTriangles,
        graphLift,
        null,
        strokeRadius * 3.0,
      ),
    );
  });
  const edges = [];
  Object.entries(layout.edges || {}).forEach(([key, route]) => {
    const [from, to] = key.split("-").map(Number);
    const points = [
      arrayToVector(layout.vertices[String(from)]),
      ...route.map(arrayToVector),
      arrayToVector(layout.vertices[String(to)]),
    ];
    const displayPoints = refineManualSurfacePath(
      points,
      surfaceTriangles,
      graphLift,
      radius,
      strokeRadius,
    );
    const start = vertices.get(from);
    const end = vertices.get(to);
    if (start && displayPoints.length) displayPoints[0] = start.clone();
    if (end && displayPoints.length)
      displayPoints[displayPoints.length - 1] = end.clone();
    edges.push({
      key,
      ends: [from, to],
      segment: [from, to],
      points: displayPoints,
    });
  });
  return {
    geometry: parsed.geometry,
    center,
    radius,
    strokeRadius,
    normalAt,
    vertices,
    edges,
  };
}

function mapPreparedManualLayout(baseRenderData, automorphism) {
  const vertices = new Map();
  const edges = [];
  for (const [vertex, point] of baseRenderData.vertices.entries()) {
    vertices.set(automorphism[vertex], point.clone());
  }
  for (const edge of baseRenderData.edges) {
    const mappedFrom = automorphism[edge.ends[0]];
    const mappedTo = automorphism[edge.ends[1]];
    edges.push({
      key: edgeKey(mappedFrom, mappedTo),
      ends: [mappedFrom, mappedTo],
      segment: [mappedFrom, mappedTo],
      points: edge.points.map((point) => point.clone()),
    });
  }
  return { vertices, edges };
}

function findAutomorphism(sourceRotation, targetRotation) {
  for (const permutation of k33Automorphisms) {
    if (
      rotationsMatch(
        applyAutomorphism(sourceRotation, permutation),
        targetRotation,
      )
    )
      return permutation;
  }
  return null;
}

function applyAutomorphism(rotation, permutation) {
  const mapped = Array.from({ length: rotation.length }, () => []);
  rotation.forEach((neighbors, vertex) => {
    mapped[permutation[vertex]] = neighbors.map(
      (neighbor) => permutation[neighbor],
    );
  });
  return mapped;
}

function rotationsMatch(actual, expected) {
  return actual.every((neighbors, vertex) =>
    cyclicOrderEqual(neighbors, expected[vertex]),
  );
}

function cyclicOrderEqual(actual, expected) {
  if (actual.length !== expected.length) return false;
  return expected.some((_, shift) =>
    actual.every(
      (value, index) => value === expected[(index + shift) % expected.length],
    ),
  );
}

function makeK33Automorphisms() {
  const permutations = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
  ];
  const automorphisms = [];
  for (const left of permutations) {
    for (const right of permutations) {
      automorphisms.push([
        left[0],
        left[1],
        left[2],
        3 + right[0],
        3 + right[1],
        3 + right[2],
      ]);
      automorphisms.push([
        3 + left[0],
        3 + left[1],
        3 + left[2],
        right[0],
        right[1],
        right[2],
      ]);
    }
  }
  return automorphisms;
}

function requestModel(rotation, outputFormat = "3d") {
  return new Promise((resolve, reject) => {
    const socket = new WebSocket(
      `${location.protocol === "https:" ? "wss:" : "ws:"}//${location.host}/stream_calc_genus`,
    );
    let done = false;
    socket.onopen = () => {
      socket.send(JSON.stringify({ alg: "none", outputFormat, adj: rotation }));
    };
    socket.onmessage = (event) => {
      const separator = event.data.indexOf(":");
      const type =
        separator === -1 ? event.data : event.data.slice(0, separator);
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
      }
    };
    socket.onerror = () => {
      if (!done) reject(new Error("Could not load the 3D model"));
    };
    socket.onclose = () => {
      if (!done)
        reject(
          new Error("3D model request closed before a model was returned"),
        );
    };
  });
}

function prefetchNearby() {
  const genusOne = systems.filter((system) => system.genus === 1);
  let cursor = 0;
  const pump = async () => {
    if (cursor >= genusOne.length) return;
    const system = genusOne[cursor++];
    const key = rotationKey(system.rotation);
    if (!modelCache.has(key)) {
      try {
        await getModel(system);
      } catch {
        return;
      }
    }
    setTimeout(pump, 80);
  };
  pump();
}

function buildModelGroup(model) {
  if (model.manualLayout) return buildManualLayoutModelGroup(model);

  const parsed = parseObj(model.obj);
  parsed.geometry.computeBoundingBox();
  const center = new THREE.Vector3();
  parsed.geometry.boundingBox.getCenter(center);
  parsed.geometry.translate(-center.x, -center.y, -center.z);
  parsed.geometry.computeBoundingSphere();
  state.surfaceCenter.copy(center);

  const group = new THREE.Group();
  const surfaceMaterial = new THREE.MeshStandardMaterial({
    color: SURFACE,
    roughness: 0.68,
    metalness: 0.02,
    side: THREE.DoubleSide,
    transparent: true,
    opacity: 1,
  });
  const surface = new THREE.Mesh(parsed.geometry, surfaceMaterial);
  group.add(surface);

  const graphMaterial = makeBasicMaterial(BLACK, 1, {
    depthTest: true,
    polygonOffset: true,
    polygonOffsetFactor: -2,
    polygonOffsetUnits: -2,
    transparent: false,
  });
  const pointMaterial = makeBasicMaterial(0xf4f4ef, 1, {
    depthTest: true,
    polygonOffset: true,
    polygonOffsetFactor: -2,
    polygonOffsetUnits: -2,
    transparent: false,
  });
  const pathsByEdge = new Map();
  const vertexPositions = new Map();
  const radius = parsed.geometry.boundingSphere?.radius || 1;
  const strokeRadius = Math.max(radius * 0.003, 0.0046);
  state.surfaceStrokeRadius = strokeRadius;

  for (const line of parsed.graphLines) {
    const centered = line.points.map((p) => p.clone().sub(center));
    const displayPoints = centered;
    const tube = makeTube(
      displayPoints,
      strokeRadius,
      graphMaterial,
      Math.max(8, displayPoints.length - 1),
    );
    tube.userData.edge = edgeKey(line.ends[0], line.ends[1]);
    group.add(tube);
    addTubeCaps(displayPoints, strokeRadius, graphMaterial, group);
    const key = edgeKey(line.ends[0], line.ends[1]);
    if (!pathsByEdge.has(key)) pathsByEdge.set(key, []);
    pathsByEdge.get(key).push({
      ends: line.ends,
      segment: line.segment,
      points: displayPoints,
    });
  }

  const pointGeometry = new THREE.SphereGeometry(strokeRadius * 1.9, 18, 12);
  for (const point of parsed.graphPoints) {
    const pos = point.position.clone().sub(center);
    vertexPositions.set(point.label, pos);
    const dot = new THREE.Mesh(pointGeometry, pointMaterial);
    dot.position.copy(pos);
    group.add(dot);
    const label = makeTextSprite(
      String(point.label),
      Math.max(radius * 0.085, 0.13),
      { depthTest: true },
    );
    const labelPos = point.labelPosition
      ? point.labelPosition.clone().sub(center)
      : pos.clone().multiplyScalar(1.035);
    label.position.copy(labelPos);
    group.add(label);
  }

  const setOpacity = (opacity, solid = false) => {
    const clamped = Math.max(0, Math.min(1, opacity));
    const materialOpacity = solid ? 1 : clamped;
    surfaceMaterial.transparent = !solid;
    surfaceMaterial.opacity = materialOpacity;
    graphMaterial.transparent = !solid;
    graphMaterial.opacity = materialOpacity;
    pointMaterial.transparent = !solid;
    pointMaterial.opacity = materialOpacity;
    surfaceMaterial.needsUpdate = true;
    graphMaterial.needsUpdate = true;
    pointMaterial.needsUpdate = true;
    group.traverse((child) => {
      if (child.isSprite && child.material) {
        child.material.transparent = true;
        child.material.opacity = materialOpacity;
      }
    });
  };
  group.userData.dispose = () => {
    parsed.geometry.dispose();
    surfaceMaterial.dispose();
    graphMaterial.dispose();
    pointMaterial.dispose();
    pointGeometry.dispose();
    disposeGroupChildren(group);
  };
  return {
    group,
    pathsByEdge,
    vertexPositions,
    setOpacity,
    normalAt: torusNormal,
  };
}

function buildManualLayoutModelGroup(model) {
  const data = model.manualSurfaceData;
  const surfaceGeometry = data.geometry.clone();
  const normalAt = data.normalAt;
  state.surfaceCenter.copy(data.center);
  const group = new THREE.Group();
  const surfaceMaterial = new THREE.MeshStandardMaterial({
    color: SURFACE,
    roughness: 0.68,
    metalness: 0.02,
    side: THREE.DoubleSide,
    transparent: true,
    opacity: 1,
  });
  const surface = new THREE.Mesh(surfaceGeometry, surfaceMaterial);
  group.add(surface);

  const graphMaterial = makeBasicMaterial(BLACK, 1, {
    depthTest: true,
    polygonOffset: true,
    polygonOffsetFactor: -2,
    polygonOffsetUnits: -2,
    transparent: false,
  });
  const pointMaterial = makeBasicMaterial(0xf4f4ef, 1, {
    depthTest: true,
    polygonOffset: true,
    polygonOffsetFactor: -2,
    polygonOffsetUnits: -2,
    transparent: false,
  });
  const pathsByEdge = new Map();
  const vertexPositions = new Map(model.manualLayout.vertices);
  const radius = data.radius;
  const strokeRadius = data.strokeRadius;
  state.surfaceStrokeRadius = strokeRadius;

  for (const edge of model.manualLayout.edges) {
    const displayPoints = edge.points.map((point) => point.clone());
    const tube = makeTube(
      displayPoints,
      strokeRadius,
      graphMaterial,
      Math.max(16, displayPoints.length - 1),
    );
    tube.userData.edge = edge.key;
    group.add(tube);
    addTubeCaps(displayPoints, strokeRadius, graphMaterial, group);
    if (!pathsByEdge.has(edge.key)) pathsByEdge.set(edge.key, []);
    pathsByEdge.get(edge.key).push({
      ends: edge.ends,
      segment: edge.segment,
      points: displayPoints,
    });
  }

  const pointGeometry = new THREE.SphereGeometry(strokeRadius * 2.25, 18, 12);
  for (const [vertexLabel, pos] of vertexPositions.entries()) {
    const dot = new THREE.Mesh(pointGeometry, pointMaterial);
    dot.position.copy(pos);
    group.add(dot);
    const labelSprite = makeTextSprite(
      String(vertexLabel),
      Math.max(radius * 0.085, 0.13),
      { depthTest: true },
    );
    labelSprite.position
      .copy(pos)
      .addScaledVector(normalAt(pos), strokeRadius * 8.0);
    group.add(labelSprite);
  }

  const setOpacity = (opacity, solid = false) => {
    const clamped = Math.max(0, Math.min(1, opacity));
    const materialOpacity = solid ? 1 : clamped;
    surfaceMaterial.transparent = !solid;
    surfaceMaterial.opacity = materialOpacity;
    graphMaterial.transparent = !solid;
    graphMaterial.opacity = materialOpacity;
    pointMaterial.transparent = !solid;
    pointMaterial.opacity = materialOpacity;
    surfaceMaterial.needsUpdate = true;
    graphMaterial.needsUpdate = true;
    pointMaterial.needsUpdate = true;
    group.traverse((child) => {
      if (child.isSprite && child.material) {
        child.material.transparent = true;
        child.material.opacity = materialOpacity;
      }
    });
  };
  group.userData.dispose = () => {
    surfaceGeometry.dispose();
    surfaceMaterial.dispose();
    graphMaterial.dispose();
    pointMaterial.dispose();
    pointGeometry.dispose();
    disposeGroupChildren(group);
  };
  return { group, pathsByEdge, vertexPositions, setOpacity, normalAt };
}

function parseObj(objText) {
  const vertices = [new THREE.Vector3()];
  const uvs = [[0, 0]];
  const positions = [];
  const texcoords = [];
  const indices = [];
  const graphLines = [];
  const graphPoints = [];
  const graphPointLabels = new Map();
  const cornerIndices = new Map();
  let pendingEdge = null;

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
    if (line.startsWith("# graph_edge ")) {
      const parts = line.split(/\s+/);
      pendingEdge = {
        ends: [Number(parts[2]) - 1, Number(parts[3]) - 1],
        segment: [Number(parts[5]) - 1, Number(parts[6]) - 1],
      };
      continue;
    }
    if (line.startsWith("# graph_vertex_label ")) {
      const parts = line.split(/\s+/);
      const vertexIndex = Number(parts[2]);
      const label = Number(parts[3]) - 1;
      const labelPosition =
        parts.length >= 7
          ? new THREE.Vector3(
              Number(parts[4]),
              Number(parts[5]),
              Number(parts[6]),
            )
          : null;
      graphPointLabels.set(vertexIndex, { label, labelPosition });
      continue;
    }
    if (line === "" || line.startsWith("#")) continue;
    const parts = line.split(/\s+/);
    if (parts[0] === "v") {
      vertices.push(
        new THREE.Vector3(Number(parts[1]), Number(parts[2]), Number(parts[3])),
      );
    } else if (parts[0] === "vt") {
      uvs.push([Number(parts[1]), Number(parts[2])]);
    } else if (parts[0] === "f") {
      const face = parts.slice(1).map(addCorner);
      for (let i = 1; i < face.length - 1; i++)
        indices.push(face[0], face[i], face[i + 1]);
    } else if (parts[0] === "l") {
      const points = parts
        .slice(1)
        .map((token) => vertices[Number(token.split("/")[0])])
        .filter(Boolean);
      if (points.length >= 2)
        graphLines.push({ ...(pendingEdge || {}), points });
      pendingEdge = null;
    } else if (parts[0] === "p") {
      for (const token of parts.slice(1)) {
        const vertexIndex = Number(token.split("/")[0]);
        const position = vertices[vertexIndex];
        const labelInfo = graphPointLabels.get(vertexIndex);
        if (position && labelInfo) {
          graphPoints.push({
            position,
            label: labelInfo.label,
            labelPosition: labelInfo.labelPosition,
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
  return { geometry, graphLines, graphPoints };
}

function buildSurfaceTriangles(geometry) {
  const positions = geometry.getAttribute("position");
  const index = geometry.index;
  const triangles = [];
  const a = new THREE.Vector3();
  const b = new THREE.Vector3();
  const c = new THREE.Vector3();
  const ab = new THREE.Vector3();
  const ac = new THREE.Vector3();
  const normal = new THREE.Vector3();
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

function projectToSurface(point, triangles) {
  const closest = new THREE.Vector3();
  const candidate = new THREE.Vector3();
  let bestDistanceSq = Infinity;
  let bestNormal = new THREE.Vector3(0, 0, 1);
  for (const triangle of triangles) {
    closestPointOnTriangle(
      point,
      triangle.a,
      triangle.b,
      triangle.c,
      candidate,
    );
    const distanceSq = point.distanceToSquared(candidate);
    if (distanceSq < bestDistanceSq) {
      bestDistanceSq = distanceSq;
      closest.copy(candidate);
      bestNormal = triangle.normal;
    }
  }
  if (!Number.isFinite(bestDistanceSq))
    return { point: point.clone(), normal: bestNormal.clone() };
  return { point: closest, normal: bestNormal.clone() };
}

function orientedProjectToSurface(
  point,
  triangles,
  previousNormal = null,
  maxSnap = Infinity,
) {
  const projection = projectToSurface(point, triangles);
  const normal = projection.normal.clone();
  if (
    Number.isFinite(maxSnap) &&
    point.distanceToSquared(projection.point) > maxSnap * maxSnap
  ) {
    return {
      point: point.clone(),
      normal: previousNormal ? previousNormal.clone() : normal,
    };
  }
  const offset = point.clone().sub(projection.point);
  if (offset.lengthSq() > 1e-12) {
    if (normal.dot(offset) < 0) normal.negate();
  } else if (previousNormal && normal.dot(previousNormal) < 0) {
    normal.negate();
  }
  if (previousNormal && normal.dot(previousNormal) < -0.35) normal.negate();
  return { point: projection.point, normal };
}

function liftPointToSurface(
  point,
  triangles,
  lift,
  previousNormal = null,
  maxSnap = Infinity,
) {
  const projection = orientedProjectToSurface(
    point,
    triangles,
    previousNormal,
    maxSnap,
  );
  return projection.point.clone().addScaledVector(projection.normal, lift);
}

function refineManualSurfacePath(
  points,
  triangles,
  lift,
  surfaceRadius,
  strokeRadius,
) {
  const clean = points.filter(Boolean).map((point) => point.clone());
  if (clean.length < 2)
    return clean.map((point) => liftPointToSurface(point, triangles, lift));

  const length = polylineLength(clean);
  const spacing = Math.max(strokeRadius * 3.5, surfaceRadius * 0.0065, 0.012);
  const sampleCount = Math.max(32, Math.min(220, Math.ceil(length / spacing)));
  const refined = [];
  let previousNormal = null;
  const maxSnap = Math.max(strokeRadius * 4.0, surfaceRadius * 0.006, 0.018);
  for (let i = 0; i <= sampleCount; i++) {
    const t = i / sampleCount;
    const sample = samplePolyline(clean, t);
    const projection = orientedProjectToSurface(
      sample,
      triangles,
      previousNormal,
      maxSnap,
    );
    previousNormal = projection.normal.clone();
    refined.push(
      projection.point.clone().addScaledVector(projection.normal, lift),
    );
  }
  return removeNearDuplicatePoints(refined, strokeRadius * 0.16);
}

function samplePolyline(points, t) {
  if (points.length === 1) return points[0].clone();
  const total = polylineLength(points);
  if (total < 1e-8) return points[0].clone();
  const target = total * Math.max(0, Math.min(1, t));
  let covered = 0;
  for (let i = 0; i < points.length - 1; i++) {
    const span = points[i].distanceTo(points[i + 1]);
    if (covered + span >= target) {
      const local = span > 1e-8 ? (target - covered) / span : 0;
      return new THREE.Vector3().lerpVectors(points[i], points[i + 1], local);
    }
    covered += span;
  }
  return points[points.length - 1].clone();
}

function removeNearDuplicatePoints(points, epsilon) {
  if (points.length < 2) return points;
  const kept = [points[0]];
  const thresholdSq = epsilon * epsilon;
  for (let i = 1; i < points.length; i++) {
    if (points[i].distanceToSquared(kept[kept.length - 1]) > thresholdSq)
      kept.push(points[i]);
  }
  if (kept.length === 1 && points.length > 1)
    kept.push(points[points.length - 1]);
  return kept;
}

function polylineLength(points) {
  let total = 0;
  for (let i = 0; i < points.length - 1; i++)
    total += points[i].distanceTo(points[i + 1]);
  return total;
}

function closestPointOnTriangle(point, a, b, c, target) {
  const ab = b.clone().sub(a);
  const ac = c.clone().sub(a);
  const ap = point.clone().sub(a);
  const d1 = ab.dot(ap);
  const d2 = ac.dot(ap);
  if (d1 <= 0 && d2 <= 0) return target.copy(a);

  const bp = point.clone().sub(b);
  const d3 = ab.dot(bp);
  const d4 = ac.dot(bp);
  if (d3 >= 0 && d4 <= d3) return target.copy(b);

  const vc = d1 * d4 - d3 * d2;
  if (vc <= 0 && d1 >= 0 && d3 <= 0) {
    const v = d1 / (d1 - d3);
    return target.copy(a).addScaledVector(ab, v);
  }

  const cp = point.clone().sub(c);
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
    return target.copy(b).addScaledVector(c.clone().sub(b), w);
  }

  const denom = 1 / (va + vb + vc);
  const v = vb * denom;
  const w = vc * denom;
  return target.copy(a).addScaledVector(ab, v).addScaledVector(ac, w);
}

function highlightDart(dart, color = BLUE) {
  clearGroup(state.highlightGroup);
  clearActiveList();
  const chip = el.rotationList.querySelector(
    `[data-dart="${dart.from}-${dart.to}"]`,
  );
  chip?.classList.add("active");
  chip?.closest(".rotation-row")?.classList.add("active");
  highlightVertex(dart.from, color);
  if (state.phase === "surface") highlightSurfaceDart(dart, color);
  else highlightFlatDart(dart, color);
}

function highlightFlatDart(dart, color) {
  addFlatDartVisual(dart, color, state.highlightGroup, 0.026, true);
}

function addTraceDart(dart, color) {
  addFlatDartVisual(dart, color, state.traceGroup, 0.018, true);
}

function addFlatDartVisual(dart, color, group, radius, arrow) {
  const from = flatPosition(dart.from);
  const to = flatPosition(dart.to);
  addDartVisualBetween(from, to, color, group, radius, arrow);
}

function addDartVisualBetween(from, to, color, group, radius, arrow) {
  const material = makeBasicMaterial(color, 1, { depthTest: false });
  const tube = makeTube([from, to], radius, material, 40);
  tube.renderOrder = 20;
  group.add(tube);
  if (arrow)
    group.add(makeArrowHead(from, to, color, radius * 4.0, radius * 8.2));
}

function highlightSurfaceDart(dart, color) {
  const segments = state.surfacePaths.get(edgeKey(dart.from, dart.to)) || [];
  if (segments.length === 0) return;
  const material = makeBasicMaterial(color, 1, { depthTest: false });
  let arrowPoints = null;

  for (const segment of segments) {
    const points = segment.points.map((point) => point.clone());
    if (points.length < 2) continue;
    const tube = makeTube(
      points,
      state.surfaceStrokeRadius * 1.8,
      material,
      Math.max(8, points.length - 1),
    );
    tube.renderOrder = 30;
    state.highlightGroup.add(tube);

    if (segment.segment?.[1] === dart.to) {
      arrowPoints = points;
    } else if (segment.segment?.[0] === dart.to) {
      arrowPoints = [...points].reverse();
    }
  }

  if (arrowPoints && arrowPoints.length >= 2) {
    const headFrom = arrowPoints[Math.max(0, arrowPoints.length - 8)];
    const headTo = arrowPoints[arrowPoints.length - 1];
    state.highlightGroup.add(
      makeArrowHead(
        headFrom,
        headTo,
        color,
        state.surfaceStrokeRadius * 5.4,
        state.surfaceStrokeRadius * 11.0,
      ),
    );
  }
}

function animateCounterclockwiseArrow(vertex, token) {
  const started = performance.now();
  const duration = 900;
  const update = () => {
    if (token !== state.sequenceToken || state.phase !== "surface") return;
    const progress = Math.min(1, (performance.now() - started) / duration);
    drawCounterclockwiseArrow(vertex, easeOut(progress));
    if (progress < 1) requestAnimationFrame(update);
  };
  update();
}

function drawCounterclockwiseArrow(vertex, progress) {
  clearGroup(state.arrowGroup);
  const center = state.surfaceVertices.get(vertex);
  if (!center) return;
  const normal = (state.surfaceNormalAt || torusNormal)(center)
    .clone()
    .normalize();
  if (normal.lengthSq() < 1e-8) normal.set(0, 0, 1);
  const basisA = new THREE.Vector3(0, 0, 1).cross(normal);
  if (basisA.lengthSq() < 1e-5) basisA.set(1, 0, 0);
  basisA.normalize();
  const basisB = normal.clone().cross(basisA).normalize();
  const radius = 0.22;
  const points = [];
  const total = Math.max(0.08, progress) * Math.PI * 1.65;
  const steps = Math.max(5, Math.round(42 * progress));
  for (let i = 0; i <= steps; i++) {
    const theta = Math.PI * 0.72 + (i / steps) * total;
    const p = center
      .clone()
      .addScaledVector(normal, state.surfaceStrokeRadius * 9.5)
      .addScaledVector(basisA, Math.cos(theta) * radius)
      .addScaledVector(basisB, Math.sin(theta) * radius);
    points.push(p);
  }
  const material = makeBasicMaterial(BLUE, 0.95, { depthTest: false });
  state.arrowGroup.add(makeTube(points, 0.009, material, Math.max(8, steps)));
  if (points.length >= 2) {
    state.arrowGroup.add(
      makeArrowHead(
        points[points.length - 2],
        points[points.length - 1],
        BLUE,
        0.045,
        0.095,
      ),
    );
  }
}

function highlightVertex(vertex, color = BLUE) {
  clearGroup(state.vertexHighlightGroup);
  const position =
    state.phase === "surface"
      ? state.surfaceVertices.get(vertex)
      : flatPosition(vertex);
  if (!position) return;
  const radius =
    state.phase === "surface" ? state.surfaceStrokeRadius * 4.0 : 0.115;
  const material = makeBasicMaterial(color, 1, { depthTest: false });
  const dot = new THREE.Mesh(
    new THREE.SphereGeometry(radius, 24, 16),
    material,
  );
  dot.position.copy(position);
  dot.renderOrder = 40;
  state.vertexHighlightGroup.add(dot);
}

function addTubeCaps(points, radius, material, group) {
  if (points.length === 0) return;
  const geometry = new THREE.SphereGeometry(radius * 1.08, 10, 8);
  const first = new THREE.Mesh(geometry, material);
  first.position.copy(points[0]);
  group.add(first);
  if (points.length > 1) {
    const last = new THREE.Mesh(geometry, material);
    last.position.copy(points[points.length - 1]);
    group.add(last);
  }
}

function torusNormal(point) {
  const major = 1.25;
  const u = Math.atan2(point.y, point.x);
  const tubeCenter = new THREE.Vector3(
    major * Math.cos(u),
    major * Math.sin(u),
    0,
  );
  return point.clone().sub(tubeCenter).normalize();
}

function clearActiveList() {
  el.rotationList
    .querySelectorAll(".active")
    .forEach((node) => node.classList.remove("active"));
}

function makeTextSprite(text, size, options = {}) {
  const canvas = document.createElement("canvas");
  const context = canvas.getContext("2d");
  const fontSize = 52;
  const padding = 16;
  const label = String(text);
  context.font = `800 ${fontSize}px system-ui, -apple-system, sans-serif`;
  const metrics = context.measureText(label);
  canvas.width = Math.ceil(metrics.width + padding * 2);
  canvas.height = fontSize + padding * 2;
  context.font = `800 ${fontSize}px system-ui, -apple-system, sans-serif`;
  context.textBaseline = "middle";
  context.lineWidth = 9;
  context.lineJoin = "round";
  context.strokeStyle = "rgba(247, 247, 242, 0.98)";
  context.fillStyle = options.color || "#171a1f";
  context.strokeText(label, padding, canvas.height / 2);
  context.fillText(label, padding, canvas.height / 2);
  const texture = new THREE.CanvasTexture(canvas);
  texture.colorSpace = THREE.SRGBColorSpace;
  const material = new THREE.SpriteMaterial({
    map: texture,
    transparent: true,
    opacity: options.opacity ?? 1,
    depthTest: options.depthTest ?? false,
    depthWrite: false,
  });
  const sprite = new THREE.Sprite(material);
  sprite.scale.set(size * (canvas.width / canvas.height), size, 1);
  sprite.renderOrder = 50;
  sprite.userData.dispose = () => {
    texture.dispose();
    material.dispose();
  };
  return sprite;
}

function makeTube(points, radius, material, segments = 32) {
  const clean = points.filter(Boolean).map((point) => point.clone());
  if (clean.length < 2) {
    const mesh = new THREE.Mesh(
      new THREE.SphereGeometry(radius, 8, 6),
      material,
    );
    if (clean[0]) mesh.position.copy(clean[0]);
    return mesh;
  }
  const path = new THREE.CurvePath();
  for (let i = 0; i < clean.length - 1; i++) {
    if (clean[i].distanceToSquared(clean[i + 1]) > 1e-10) {
      path.add(new THREE.LineCurve3(clean[i], clean[i + 1]));
    }
  }
  if (path.curves.length === 0) {
    const mesh = new THREE.Mesh(
      new THREE.SphereGeometry(radius, 8, 6),
      material,
    );
    mesh.position.copy(clean[0]);
    return mesh;
  }
  const geometry = new THREE.TubeGeometry(
    path,
    Math.max(1, segments),
    radius,
    6,
    false,
  );
  return new THREE.Mesh(geometry, material);
}

function makeArrowHead(from, to, color, radius, height, options = {}) {
  const direction = to.clone().sub(from);
  if (direction.lengthSq() < 1e-8) direction.set(1, 0, 0);
  direction.normalize();
  const cone = new THREE.Mesh(
    new THREE.ConeGeometry(radius, height, 24),
    makeBasicMaterial(color, options.opacity ?? 1, {
      depthTest: options.depthTest ?? false,
    }),
  );
  const backoff = options.tipAtTarget ? 0.5 : 0.18;
  cone.position.copy(to.clone().addScaledVector(direction, -height * backoff));
  cone.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), direction);
  cone.renderOrder = options.renderOrder ?? 35;
  return cone;
}

function makeBasicMaterial(color, opacity = 1, options = {}) {
  return new THREE.MeshBasicMaterial({
    color,
    transparent: opacity < 1 || options.transparent !== false,
    opacity,
    depthTest: options.depthTest ?? true,
    depthWrite: false,
    polygonOffset: options.polygonOffset ?? false,
    polygonOffsetFactor: options.polygonOffsetFactor ?? 0,
    polygonOffsetUnits: options.polygonOffsetUnits ?? 0,
  });
}

function setCameraPose(position, target) {
  state.cameraToken++;
  camera.position.copy(position);
  controls.target.copy(target);
  camera.near = 0.01;
  camera.far = 100;
  camera.updateProjectionMatrix();
  controls.update();
}

function animateCamera(position, target, duration) {
  const token = ++state.cameraToken;
  const startPosition = camera.position.clone();
  const startTarget = controls.target.clone();
  const started = performance.now();
  return new Promise((resolve) => {
    const tick = () => {
      if (token !== state.cameraToken) {
        resolve(false);
        return;
      }
      const t = Math.min(1, (performance.now() - started) / duration);
      const eased = easeInOut(t);
      camera.position.lerpVectors(startPosition, position, eased);
      controls.target.lerpVectors(startTarget, target, eased);
      camera.near = 0.01;
      camera.far = 100;
      camera.updateProjectionMatrix();
      controls.update();
      if (t < 1) {
        requestAnimationFrame(tick);
      } else {
        resolve(true);
      }
    };
    tick();
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

function disposeModelGroup() {
  if (!state.modelGroup) return;
  scene.remove(state.modelGroup);
  disposeGroup(state.modelGroup);
  state.modelGroup = null;
  state.surfacePaths = new Map();
  state.surfaceVertices = new Map();
  state.surfaceNormalAt = null;
  state.finalOpacity = null;
}

function clearGroup(group) {
  while (group.children.length) {
    const child = group.children.pop();
    disposeObject(child);
  }
}

function disposeGroup(group) {
  group.userData.dispose?.();
  disposeObject(group);
}

function disposeGroupChildren(group) {
  for (const child of group.children) disposeObject(child);
}

function disposeObject(object) {
  object.traverse?.((child) => {
    if (child.geometry) child.geometry.dispose();
    if (child.material) {
      const materials = Array.isArray(child.material)
        ? child.material
        : [child.material];
      materials.forEach((material) => {
        if (material.map) material.map.dispose();
        material.dispose();
      });
    }
    if (child.userData?.dispose && child !== object) child.userData.dispose();
  });
}

function setGroupOpacity(group, opacity) {
  if (!group) return;
  group.traverse((child) => {
    if (!child.material) return;
    const materials = Array.isArray(child.material)
      ? child.material
      : [child.material];
    materials.forEach((material) => {
      material.opacity = opacity;
      material.transparent = true;
    });
  });
}

function dartKey(from, to) {
  return `${from}-${to}`;
}

function edgeKey(a, b) {
  return a < b ? `${a}-${b}` : `${b}-${a}`;
}

function rotationKey(rotation) {
  return rotation.map((neighbors) => neighbors.join(",")).join("|");
}

function clampRotationNumber(value) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) return state.index + 1;
  return Math.min(systems.length, Math.max(1, Math.round(parsed)));
}

function delay(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function nextFrame() {
  return new Promise((resolve) => requestAnimationFrame(resolve));
}

function easeInOut(t) {
  const clamped = Math.max(0, Math.min(1, t));
  return clamped * clamped * (3 - 2 * clamped);
}

function lerpScalar(a, b, t) {
  return a + (b - a) * t;
}

function arrayToVector(value) {
  return new THREE.Vector3(
    Number(value[0]),
    Number(value[1]),
    Number(value[2]),
  );
}

function easeOut(t) {
  const clamped = Math.max(0, Math.min(1, t));
  return 1 - Math.pow(1 - clamped, 3);
}
