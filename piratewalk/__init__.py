import simplejson as json
import urllib2

import os
import os.path

import logging

import Geohash
import cairo
import Flickr.API

import types
import elementtree.ElementTree as ET

from math import sin, cos, acos, radians, degrees

import ModestMaps
import modestMMarkers

import sqlite3

import time
from datetime import tzinfo, timedelta, datetime

ZERO = timedelta(0)
HOUR = timedelta(hours=1)

class UTC(tzinfo):

    def utcoffset(self, dt):
        return ZERO

    def tzname(self, dt):
        return "UTC"

    def dst(self, dt):
        return ZERO

class piratewalk:

	def __init__(self, **kwargs):

		self.palette = 'pink'

		self.method = kwargs.get('method', 'extent')
		self.width = kwargs.get('width', 2048)
		self.height = kwargs.get('height', 1024)
		self.zoom = kwargs.get('zoom', 16)

		self.max_distance = kwargs.get('max_distance', .1)
		self.draw_raster_map = kwargs.get('draw_raster_map', False)

		self.mm_obj = None
		self.mm_img = None
		self.mm_markers = None

		self.geonames_cache = {}
		self.geonames_cache_db = None

		self.flickr_api = None
		self.draw_flickr_shapefiles = False

		self.flickr_cache = {}
		self.flickr_cache_db = None

		if kwargs.get('flickr_apikey', False):
			self.flickr_api = Flickr.API.API(kwargs['flickr_apikey'], None)

		if kwargs.get('draw_flickr_shapefiles', False):
			self.draw_flickr_shapefiles = True
			self.palette = 'flickr'

		if kwargs.get('geonames_cache_db'):
			self.geonames_cache_db = sqlite3.connect(kwargs['geonames_cache_db'])

		if kwargs.get('flickr_cache_db'):
			self.flickr_cache_db = sqlite3.connect(kwargs['flickr_cache_db'])

	def adjust_bbox (self, bbox, adjust) :

		swlat = bbox[0]
		swlon = bbox[1]
		nelat = bbox[2]
		nelon = bbox[3]

		adjust_ne = 1
		adjust_sw = 1

		if nelon < 0 :
			adjust_ne = - adjust_ne

		if swlon < 0 :
			adjust_sw = - adjust_sw

		dist_n = self.dist(nelat, nelon, nelat, (nelon + adjust_ne))
		dist_s = self.dist(swlat, swlon, swlat, (swlon + adjust_sw))

		swlat = swlat - (float(adjust) / float(dist_s))
		swlon = swlon - (float(adjust) / float(dist_s))
		nelat = nelat + (float(adjust) / float(dist_n))
		nelon = nelon + (float(adjust) / float(dist_n))

		return [swlat, swlon, nelat, nelon]

	def dist(self, lat1, lon1, lat2, lon2) :

		theta = lon1 - lon2
		dist = sin(radians(lat1)) * sin(radians(lat2)) +  cos(radians(lat1)) * cos(radians(lat2)) * cos(radians(theta));
		dist = acos(dist);
		dist = degrees(dist);
		return dist * 60

	def calculate_bbox_for_points (self, points) :

		sw_lat = None
		sw_lon = None
		ne_lat = None
		ne_lon = None

		for pt in points :

			lat = pt['latitude']
			lon = pt['longitude']

			if not sw_lat or lat < sw_lat :
				sw_lat = lat

			if not sw_lon or lon < sw_lon :
				sw_lon = lon

			if not ne_lat or lat > ne_lat :
				ne_lat = lat

			if not ne_lon or lon > ne_lon :
				ne_lon = lon

		return (sw_lat,sw_lon,ne_lat,ne_lon)

	def geonames_cache_fetch(self, key):

		if self.geonames_cache_db:
			db = self.geonames_cache_db.cursor()
			db.execute("SELECT data FROM geonames_roads WHERE geohash='%s'" % key)

			row = db.fetchone()

			if not row:
				return None

			try:
				data = json.loads(row[0])
			except Exception, e:
				logging.debug("failed to load cache data for %s: %s" % (key, e))
				return None

			logging.debug("return from geonames cache for key %s" % key)
			return data

		elif self.geonames_cache.get(key, False):
			return self.geonames_cache[key]

		else:
			return None

	def geonames_cache_set(self, key, data):

		if self.geonames_cache_db:

			db = self.geonames_cache_db.cursor()

			try:
				db.execute("""INSERT INTO geonames_roads (geohash, data) VALUES(?,?)""", (key, json.dumps(data)))
				self.geonames_cache_db.commit()
			except Exception, e:
				logging.debug("failed to store cache data for %s: %s" % (key, e))
				return None
		else:
			self.geonames_cache[key] = data

	def flickr_cache_fetch(self, key):

		if self.flickr_cache_db:

			db = self.flickr_cache_db.cursor()
			db.execute("SELECT data FROM pirateshapes WHERE geohash='%s'" % key)

			row = db.fetchone()

			if not row:
				return None

			try:
				data = json.loads(row[0])
			except Exception, e:
				logging.debug("failed to load cache data for %s: %s" % (key, e))
				return None

			logging.debug("return from flickr cache for key %s" % key)
			return data

		elif self.flickr_cache.get(key, False):
			return self.flickr_cache[key]

		else:
			return None

	def flickr_cache_set(self, key, data):

		if self.flickr_cache_db:

			db = self.flickr_cache_db.cursor()

			try:
				db.execute("""INSERT INTO pirateshapes (geohash, data) VALUES(?,?)""", (key, json.dumps(data)))
				self.flickr_cache_db.commit()
			except Exception, e:
				logging.debug("failed to store cache data for %s: %s" % (key, e))
				return None
		else:
			self.flickr_cache[key] = data

	def generate_polylines(self, points):

		polylines = {
			'big' : [],
			'medium' : [],
			'small' : []
			}

		for pt in points:

			gh = self.geohash_for_point(pt)
			data = self.geonames_cache_fetch(gh)

			if not data:
				req = 'http://ws.geonames.org/findNearbyStreetsOSMJSON?lat=%s&lng=%s' % (pt['latitude'], pt['longitude'])
				logging.debug(req)

				try :
					res = urllib2.urlopen(req)
					res = res.read()
					data = json.loads(res)
				except Exception, e:
					logging.error("failed to fetch %s : %s" % (req, e))
					continue

				self.geonames_cache_set(gh, data)

			#

			if not data.has_key('streetSegment'):
				logging.warning("no street segment")
				continue

			if type(data['streetSegment']) == types.DictType:
				hack = data['streetSegment']
				data['streetSegment'] = [ hack ]

			#

			for s in data['streetSegment']:

				try:
					logging.debug('segment: %s, %s' % (s['highway'], s['distance']))
				except Exception, e:
					logging.error("no distance")
					continue

				if float(s['distance']) > self.max_distance:
					logging.debug("skip segment")
					continue

				poly = []

				for pt in s['line'].split(','):
					ln, lt = pt.split(' ')
					poly.append({'latitude' : float(lt), 'longitude' : float(ln) })

				key = 'small'

				if s['highway'] in ('primary', 'secondary'):
					key = 'big'
				elif s['highway'] in ('tertiary', 'residential'):
					key = 'medium'
				else:
					key = 'small'

				polylines[key].append(poly)

		return polylines

	def mm(self, points):

		bbox = self.calculate_bbox_for_points(points)

		if self.method == 'bbox':
			bbox = self.adjust_bbox(bbox, .5)

		self.bbox = bbox

		dims = ModestMaps.Core.Point(self.width, self.height)
		sw = ModestMaps.Geo.Location(bbox[0], bbox[1])
		ne = ModestMaps.Geo.Location(bbox[2], bbox[3])

		provider = ModestMaps.builtinProviders[ 'MICROSOFT_AERIAL' ]()

		if self.method == 'bbox':
			mm_obj = ModestMaps.mapByExtentZoom(provider, sw, ne, self.zoom)
		else:
			mm_obj = ModestMaps.mapByExtent(provider, sw, ne, dims)

		self.mm_provider = provider
		self.mm_obj = mm_obj
		self.mm_markers = modestMMarkers.modestMMarkers(self.mm_obj)

		return True

	def save(self, path):

		if isinstance(self.mm_img, cairo.ImageSurface) :
			fh = open(path, 'wb')
			self.mm_img.write_to_png(fh)
			fh.close()
			return

		img = modestMMarkers.cairo2pil(self.mm_img)
		img.save(path)

	def draw_base_map(self):

		logging.debug("draw base map using %s method" % self.method)

		if self.draw_raster_map:
			logging.debug("draw base map raster tiles")
			mm_img = self.mm_obj.draw()
		else:

			if self.method == 'bbox':

				swlat, swlon, nelat, nelon = self.bbox

				nwlat = nelat
				nwlon = swlon
				selat = swlat
				selon = nelon

				nw = ModestMaps.Geo.Location(nwlat, nwlon)
				se = ModestMaps.Geo.Location(selat, selon)

				tl = self.mm_provider.locationCoordinate(nw).zoomTo(self.zoom).container()
				br = self.mm_provider.locationCoordinate(se).zoomTo(self.zoom).container()

				rows = int(br.row - tl.row)
				cols = int(br.column - tl.column)

				self.height = rows * 256
				self.width = cols * 256

			logging.debug("base map dimensions: %s, %s" % (self.width, self.height))

			# Maybe hide all of this in modestMMarkers?
			# Also make this an SVG surface? Requires tweaking in modestMMarkers.

			mm_img = cairo.ImageSurface(cairo.FORMAT_ARGB32, self.width, self.height)
			ctx = cairo.Context(mm_img)
			ctx.rectangle(0, 0, self.width, self.height)
			ctx.set_source_rgba(1, 1, 1, 1)
			ctx.fill()

		self.mm_img = mm_img
		return True

	def render_map_simple(self, points, **kwargs):

		if self.draw_flickr_shapefiles:
			flickr_data = self.flickr_shapefiles_for_points(points, **kwargs)

			if len(flickr_data['points']):
				self.mm(flickr_data['points'])
			else:
				self.mm(points)

			kwargs['draw_polylines'] = flickr_data['shapes']

		polylines = self.generate_polylines(points)
		ret = self.render_map(points, polylines, **kwargs)

		return ret

	def render_map(self, points, polylines, **kwargs):

		if not self.mm_obj:
			self.mm(points)

		if not self.draw_base_map():
			logging.error("failed to draw base map")
			return False

		road_opacity = .01
		points_opacity = .01
		polylines_opacity = .01

		polylines_colour = (0, 0, 0)
		points_colour = (.7, .7, .7)
		roads_colour = (255, 0, 132)

		if self.palette == 'flickr':
			points_colour = (1, 1, 1)
			roads_colour = (.5, 1, 1)

		if kwargs.get('draw_polylines', False):

			logging.debug("draw polylines")

			for poly in kwargs['draw_polylines']:

				self.mm_img = self.mm_markers.draw_polyline(self.mm_img, poly,
									    opacity_fill=polylines_opacity,
									    color=(0, 0, 0),
									    opacity_border=0,
									    return_as_cairo=True)

		if kwargs.get('draw_points', False):

			logging.debug("draw points")

			self.mm_img = self.mm_markers.draw_points(self.mm_img, points,
								  color=points_colour,
								  opacity_fill=points_opacity,
								  return_as_cairo=True)

		if kwargs.get('draw_points_as_line', False):

			logging.debug("draw points as lines")

			self.mm_img = self.mm_markers.draw_lines(self.mm_img, [points],
								 color=points_colour,
								 opacity=.4,
								 line_width=10,
								 return_as_cairo=True)

		if len(polylines['small']):

			logging.debug("draw small roads")

			self.mm_img = self.mm_markers.draw_lines(self.mm_img, polylines['small'],
								 line_width=2,
								 opacity=road_opacity,
								 color=roads_colour,
								 return_as_cairo=True)

		if len(polylines['medium']):

			logging.debug("draw medium roads")

			self.mm_img = self.mm_markers.draw_lines(self.mm_img, polylines['medium'],
								 line_width=4,
								 opacity=road_opacity,
								 color=roads_colour,
								 return_as_cairo=True)

		if len(polylines['big']):

			logging.debug("draw big roads")

			self.mm_img = self.mm_markers.draw_lines(self.mm_img, polylines['big'],
								 line_width=6,
								 opacity=road_opacity,
								 color=roads_colour,
								 return_as_cairo=True)

		return True

	def geohash_for_point(self, pt, precision=12):

		gh = Geohash.encode(pt['latitude'], pt['longitude'], precision=precision)
		logging.debug("geohash (%s) for %s, %s: %s" % (precision, pt['latitude'], pt['longitude'], gh))

		return gh

	def flickr_shapefiles_for_points(self, points, **kwargs):

		flickr = { 'shapes' : [], 'points' : [] }

		for pt in points:

			logging.debug("fetch woeid and shapedata for %s,%s" % (pt['latitude'], pt['longitude']))

			valid_placetypes = kwargs.get('valid_placetypes', None)

			gh = self.geohash_for_point(pt, 6)

			if valid_placetypes:
				gh = "%s#%s" % (gh, str(valid_placetypes))

			data = self.flickr_cache_fetch(gh)

			# fix this to account for placetype...

			if data:
				logging.debug("return shape data from cache")
				flickr['shapes'].append(data)

			else:

				# reverse geocode : cache me...

				args = { 'lat':pt['latitude'], 'lon':pt['longitude'], 'format':'json', 'nojsoncallback':1}

				try:
					rsp = self.flickr_api.execute_method(method='flickr.places.findByLatLon', args=args)
					data = json.loads(rsp.read())
				except Exception, e:
					logging.error("failed to reverse geocode: %s" % e)
					continue

				stat = data.get('stat', False)

				if stat != 'ok':
					logging.warning("reverse geocoding failed")
					continue

				if data['places']['total'] == 0:
					logging.debug("no results for reverse geocoding, caching as empty")
					self.flickr_cache_set(gh, [])
					continue

				#

				woeid = data['places']['place'][0]['woeid']
				placetype = int(data['places']['place'][0]['place_type_id'])

				if valid_placetypes and not placetype in valid_placetypes:
					logging.info("WOE ID %s (%s) has wrong place type: %s, caching as empty" % (woeid, gh, placetype))
					self.flickr_cache_set(gh, [])
					continue

				# places.info - cache me...

				try:
					args = { 'woe_id' : woeid, 'format' : 'json', 'nojsoncallback' : 1 }
					rsp = self.flickr_api.execute_method(method='flickr.places.getInfo', args=args)
					data = json.loads(rsp.read())
				except Exception, e:
					logging.error("failed to get info: %s" % e)
					continue

				stat = data.get('stat', False)

				if stat != 'ok':
					logging.warning("places get info failed")
					continue

				shapedata = data['place'].get('shapedata', None)

				if not shapedata:
					logging.debug("no shape for %s, caching as empty" % woeid)
					self.flickr_cache_set(gh, [])
					continue

				#

				shape = []

				for line in shapedata['polylines']['polyline']:

					for pt in line['_content'].split(' '):
						lat, lon = pt.split(',')
						shape.append({ 'latitude' : float(lat), 'longitude' : float(lon) })

					flickr['shapes'].append(shape)

				self.flickr_cache_set(gh, shape)

		#

		for line in flickr['shapes']:
			for pt in line:
				flickr['points'].append(pt)

		#

		return flickr

class kml(piratewalk):

	def draw(self, kml_files):

		points = []

		for kml in kml_files:

			logging.debug("parsing %s" % kml)
			et = ET.parse(kml)

			for c in et.findall('.//{http://www.opengis.net/kml/2.2}coordinates'):
				lon, lat, ignore = c.text.split(',')
				points.append({ 'latitude' : float(lat), 'longitude' : float(lon) })

		return self.render_map_simple(points, draw_points=True)

class georss(piratewalk):

	def draw(self, rss_files):

		points = []

		for rss in rss_files:

			logging.debug("parsing %s" % rss)
			et = ET.parse(rss)

			for c in et.findall('.//{http://www.georss.org/georss}point'):
				pt = c.text.strip()
				lat, lon = pt.split(' ')
				points.append({ 'latitude' : float(lat), 'longitude' : float(lon) })

		return self.render_map_simple(points, draw_points=True)

class gpx(piratewalk):

	def draw(self, gpx_files):
		points = []

		for gpx in gpx_files:

			logging.debug("parsing %s" % gpx)
			et = ET.parse(gpx)

			# fix me: figure out which one we need to use...

			for r in et.findall('.//{http://www.topografix.com/GPX/1/1}rtept'):
				lat = float(r.attrib['lat'])
				lon = float(r.attrib['lon'])
				points.append({ 'latitude' : float(lat), 'longitude' : float(lon) })

			for r in et.findall('.//{http://www.topografix.com/GPX/1/0}trkpt'):
				lat = float(r.attrib['lat'])
				lon = float(r.attrib['lon'])
				points.append({ 'latitude' : float(lat), 'longitude' : float(lon) })

		return self.render_map_simple(points, draw_points_as_line=True, draw_points=True)

class flickr(piratewalk):

	def photos_search(self, args):

		logging.debug("call flickr.photos.search with args: %s" % str(args))

		points = []

		current_page = 1
		num_pages = None

		if not args.get('per_page', False):
			args['per_page'] = 250

		max_pages_to_fetch = 4000 / args['per_page']

		while not num_pages or current_page <= num_pages :

			logging.debug("fetch page %s of %s from flickr" % (current_page, num_pages))

			args['page'] = current_page
			res = self.flickr_api.execute_method(method='flickr.photos.search', args=args)

			tree = ET.parse(res)
			rsp = tree.getroot()

			err = rsp.find("err")

			if err != None :
				logging.error("flickr API returned an error: %s" % err)
				break

			if not num_pages :
				num_pages = int(rsp.find('photos').attrib['pages'])
				logging.debug("total number of pages to fetch: %s" % num_pages)

			if num_pages == 0 :
				logging.warning("no results")
				break

			for ph in rsp.findall('.//photo') :

				lat = float(ph.attrib['latitude'])
				lon = float(ph.attrib['longitude'])

				if lat == 0.0 and lon == 0.0:
					continue

				points.append({ 'latitude' : lat, 'longitude' : lon })

			# please to record photo date upload and adjust min_upload_date
			# when we trigger this error...

			if current_page == max_pages_to_fetch:
				logging.warning("exceed 4000 results, giving up")
				break

			current_page += 1

		return points

	def draw_photos_search(self, args):

		points = self.photos_search(args)
		return self.render_map_simple(points, draw_points=True)

	def draw_photos_search_iterate(self, **kwargs):

		collect = kwargs.get('collect', True)
		all_points = []

		images = []

		# this is deliberately simple and not very fine-grained
		# to start with mostly because I hate working with dates
		# in python....

		ymd_start = kwargs['ymd_start']
		days_total = kwargs['days_total']
		days_offset = kwargs.get('days_offset', 7)

		root = kwargs['image_root']
		prefix = kwargs['image_prefix']

		utc = UTC()

		t = time.strptime(ymd_start, '%Y-%m-%d')
		t = list(t[:-2])
		t.append(utc)

		now = datetime(*t)

		for i in range(days_total/days_offset):

			offset = timedelta(days=days_offset)
			then = now + offset

			logging.debug("search between %s and %s" % (now, then))

			ts_now = int(time.mktime(now.timetuple()))
			ts_then = int(time.mktime(then.timetuple()))
			now = then

			if ts_now >= int(time.time()):
				logging.warning("about to start looking for photos IN THE FUTURE")
				break

			kwargs['search_args']['min_upload_date'] = ts_now
			kwargs['search_args']['max_upload_date'] = ts_then - 1

			points = self.photos_search(kwargs['search_args'])

			if collect:
				all_points.extend(points)
			else :
				all_points = points

			if len(all_points):
				mm_img = self.render_map_simple(all_points, draw_points=True)

				fname = "%s_%s.png" % (prefix, ts_now)
				path = os.path.join(root, fname)

				logging.debug("save image to %s" % path)

				self.save(path)
				images.append(path)

		return images

	def draw_user_photos(self, user_id, woeid, contacts=None):

		if not self.flickr_api:
			logging.error('no flickr API object')
			return None

		args = { 'woe_id' : woeid, 'user_id' : user_id, 'extras' : 'geo' }

		if contacts:
			args['contacts'] = contacts

		points = self.photos_search(args)
		return self.render_map_simple(points, draw_points=True)

class foursquare(piratewalk):

	def draw_history(self, history):

		utc = UTC()
		points = []

		venues = {}
		venues_date = {}
		venues_count = {}

		for root, dirname, filenames in os.walk(history):

			if len(filenames) == 0:
				continue

			for f in filenames:
				checkin = os.path.join(root, f)

				et = ET.parse(checkin)
				dt = et.find('created').text

				# I hate you so much Python...
				# Sat, 20 Feb 10 19:05:25 +0000

				t = time.strptime(dt, '%a, %d %b %y %H:%M:%S +0000')
				t = list(t[:-2])
				t.append(utc)

				dt = datetime(*t)
				offset = timedelta(hours=8)
				dt = dt - offset

				ymd = dt.strftime('%Y-%m-%d')

				venue_id = et.find('venue/id').text
				lat = float(et.find('venue/geolat').text)
				lon = float(et.find('venue/geolong').text)

				pt = { 'latitude' : lat, 'longitude' : lon }
				points.append(pt)

				if venues.has_key(venue_id):
					venues[ venue_id ]['count'] += 1
				else:
					venues[ venue_id ] = { 'count' : 1, 'loc' : pt }

				if venues_date.has_key(ymd):
					venues_date[ ymd ].append(pt)
				else:
					venues_date[ ymd ] = [ pt ]

		return self.render_map_simple(points)
