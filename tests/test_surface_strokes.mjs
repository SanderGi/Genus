// SPDX-FileCopyrightText: 2026 Alexander Metzger
// SPDX-License-Identifier: GPL-2.0-only
import assert from 'node:assert/strict';
import fs from 'node:fs';
import vm from 'node:vm';
import * as THREE from '../app/static/vendor/three.js';

const source = fs.readFileSync(new URL('../app/static/script.js', import.meta.url), 'utf8');
const context = { THREE };
vm.createContext(context);
vm.runInContext(source.slice(source.indexOf('function surfacePolylineGeometry'),
  source.indexOf('function makeGraphOverlay')), context);
const points = [[0, 0, 0], [1, 0, 0], [1, 0.000001, 0], [1, 1, 0], [1, 1, 1]]
  .map(p => new THREE.Vector3(...p));
const geometry = context.surfacePolylineGeometry(points, 0.001);
const positions = geometry.getAttribute('position');
assert.equal(positions.count, points.length * 6);
assert.equal(geometry.index.count, (points.length - 1) * 36);
for (let i = 0; i < points.length; i++) {
  const center = new THREE.Vector3();
  for (let side = 0; side < 6; side++) {
    center.add(new THREE.Vector3().fromBufferAttribute(positions, i * 6 + side));
  }
  center.multiplyScalar(1 / 6);
  assert.ok(center.distanceTo(points[i]) < 1e-7, 'Surface centerline knot changed');
}
console.log('Surface stroke geometry preserves every knot and segment.');
